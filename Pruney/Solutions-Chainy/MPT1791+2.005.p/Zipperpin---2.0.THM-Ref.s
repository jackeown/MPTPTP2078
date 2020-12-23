%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsXD955iFi

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:45 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 345 expanded)
%              Number of leaves         :   29 ( 111 expanded)
%              Depth                    :   26
%              Number of atoms          : 1624 (4584 expanded)
%              Number of equality atoms :   87 ( 226 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( u1_pre_topc @ X11 ) )
      | ( ( u1_pre_topc @ X11 )
        = ( k5_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X13 @ X12 ) )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X13 @ X12 ) )
        = ( k5_tmap_1 @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('60',plain,(
    ! [X7: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X7 ) @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v3_pre_topc @ X4 @ X5 )
      | ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('71',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X10 @ ( u1_pre_topc @ X11 ) )
      | ( ( u1_pre_topc @ X11 )
        = ( k5_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('77',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X13 @ X12 ) )
        = ( k5_tmap_1 @ X13 @ X12 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('81',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X13 @ X12 ) )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X2: $i] :
      ( ~ ( v1_pre_topc @ X2 )
      | ( X2
        = ( g1_pre_topc @ ( u1_struct_0 @ X2 ) @ ( u1_pre_topc @ X2 ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( v1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('103',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100','101','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k5_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('109',plain,
    ( ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
      = ( k5_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( u1_pre_topc @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['102','103'])).

thf('120',plain,
    ( ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( u1_pre_topc @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['116','117','118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
      = ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( u1_pre_topc @ X11 )
       != ( k5_tmap_1 @ X11 @ X10 ) )
      | ( r2_hidden @ X10 @ ( u1_pre_topc @ X11 ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','130'])).

thf('132',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ ( u1_pre_topc @ X5 ) )
      | ( v3_pre_topc @ X4 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('135',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','58','59','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dsXD955iFi
% 0.16/0.36  % Computer   : n021.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:39:34 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 0.48/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.72  % Solved by: fo/fo7.sh
% 0.48/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.72  % done 342 iterations in 0.239s
% 0.48/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.72  % SZS output start Refutation
% 0.48/0.72  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.48/0.72  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.48/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.72  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.48/0.72  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.48/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.48/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.48/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.48/0.72  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.48/0.72  thf(t106_tmap_1, conjecture,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.72           ( ( v3_pre_topc @ B @ A ) <=>
% 0.48/0.72             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.48/0.72               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.72    (~( ![A:$i]:
% 0.48/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.72            ( l1_pre_topc @ A ) ) =>
% 0.48/0.72          ( ![B:$i]:
% 0.48/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.72              ( ( v3_pre_topc @ B @ A ) <=>
% 0.48/0.72                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.48/0.72                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.48/0.72    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.48/0.72  thf('0', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('1', plain,
% 0.48/0.72      (~
% 0.48/0.72       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.48/0.72       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('split', [status(esa)], ['0'])).
% 0.48/0.72  thf('2', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('3', plain,
% 0.48/0.72      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('split', [status(esa)], ['2'])).
% 0.48/0.72  thf('4', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(d5_pre_topc, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( l1_pre_topc @ A ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.72           ( ( v3_pre_topc @ B @ A ) <=>
% 0.48/0.72             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.48/0.72  thf('5', plain,
% 0.48/0.72      (![X4 : $i, X5 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.48/0.72          | ~ (v3_pre_topc @ X4 @ X5)
% 0.48/0.72          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.48/0.72          | ~ (l1_pre_topc @ X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.48/0.72  thf('6', plain,
% 0.48/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.48/0.72        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.72  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('8', plain,
% 0.48/0.72      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.48/0.72        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.48/0.72  thf('9', plain,
% 0.48/0.72      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.48/0.72         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['3', '8'])).
% 0.48/0.72  thf('10', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(t103_tmap_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.72           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.48/0.72             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.72  thf('11', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.48/0.72          | ~ (r2_hidden @ X10 @ (u1_pre_topc @ X11))
% 0.48/0.72          | ((u1_pre_topc @ X11) = (k5_tmap_1 @ X11 @ X10))
% 0.48/0.72          | ~ (l1_pre_topc @ X11)
% 0.48/0.72          | ~ (v2_pre_topc @ X11)
% 0.48/0.72          | (v2_struct_0 @ X11))),
% 0.48/0.72      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.48/0.72  thf('12', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.72  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('15', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.48/0.72      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.48/0.72  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('17', plain,
% 0.48/0.72      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.48/0.72        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('clc', [status(thm)], ['15', '16'])).
% 0.48/0.72  thf('18', plain,
% 0.48/0.72      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.48/0.72         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['9', '17'])).
% 0.48/0.72  thf('19', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(t104_tmap_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( ![B:$i]:
% 0.48/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.72           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.48/0.72             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.48/0.72  thf('20', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.48/0.72          | ((u1_struct_0 @ (k6_tmap_1 @ X13 @ X12)) = (u1_struct_0 @ X13))
% 0.48/0.72          | ~ (l1_pre_topc @ X13)
% 0.48/0.72          | ~ (v2_pre_topc @ X13)
% 0.48/0.72          | (v2_struct_0 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.48/0.72  thf('21', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.72  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('24', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.48/0.72  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('26', plain,
% 0.48/0.72      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.48/0.72      inference('clc', [status(thm)], ['24', '25'])).
% 0.48/0.72  thf(abstractness_v1_pre_topc, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( l1_pre_topc @ A ) =>
% 0.48/0.72       ( ( v1_pre_topc @ A ) =>
% 0.48/0.72         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.48/0.72  thf('27', plain,
% 0.48/0.72      (![X2 : $i]:
% 0.48/0.72         (~ (v1_pre_topc @ X2)
% 0.48/0.72          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.48/0.72          | ~ (l1_pre_topc @ X2))),
% 0.48/0.72      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.48/0.72  thf('28', plain,
% 0.48/0.72      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.48/0.72          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72             (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.48/0.72        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['26', '27'])).
% 0.48/0.72  thf('29', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(dt_k6_tmap_1, axiom,
% 0.48/0.72    (![A:$i,B:$i]:
% 0.48/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.72         ( l1_pre_topc @ A ) & 
% 0.48/0.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.72       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.48/0.72         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.48/0.72         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.48/0.72  thf('30', plain,
% 0.48/0.72      (![X8 : $i, X9 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X8)
% 0.48/0.72          | ~ (v2_pre_topc @ X8)
% 0.48/0.72          | (v2_struct_0 @ X8)
% 0.48/0.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.48/0.72          | (l1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.48/0.72  thf('31', plain,
% 0.48/0.72      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | (v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.72  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('34', plain,
% 0.48/0.72      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.48/0.72      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.48/0.72  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('36', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.48/0.72      inference('clc', [status(thm)], ['34', '35'])).
% 0.48/0.72  thf('37', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('38', plain,
% 0.48/0.72      (![X8 : $i, X9 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X8)
% 0.48/0.72          | ~ (v2_pre_topc @ X8)
% 0.48/0.72          | (v2_struct_0 @ X8)
% 0.48/0.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.48/0.72          | (v1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.48/0.72  thf('39', plain,
% 0.48/0.72      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | (v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.72  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('42', plain,
% 0.48/0.72      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.48/0.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.48/0.72  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('44', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.48/0.72      inference('clc', [status(thm)], ['42', '43'])).
% 0.48/0.72  thf('45', plain,
% 0.48/0.72      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.48/0.72         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 0.48/0.72            (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('demod', [status(thm)], ['28', '36', '44'])).
% 0.48/0.72  thf('46', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('47', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.48/0.72          | ((u1_pre_topc @ (k6_tmap_1 @ X13 @ X12)) = (k5_tmap_1 @ X13 @ X12))
% 0.48/0.72          | ~ (l1_pre_topc @ X13)
% 0.48/0.72          | ~ (v2_pre_topc @ X13)
% 0.48/0.72          | (v2_struct_0 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.48/0.72  thf('48', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.48/0.72  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('51', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.48/0.72  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('53', plain,
% 0.48/0.72      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.48/0.72      inference('clc', [status(thm)], ['51', '52'])).
% 0.48/0.72  thf('54', plain,
% 0.48/0.72      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.48/0.72         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('demod', [status(thm)], ['45', '53'])).
% 0.48/0.72  thf('55', plain,
% 0.48/0.72      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.48/0.72          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.48/0.72         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('sup+', [status(thm)], ['18', '54'])).
% 0.48/0.72  thf('56', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.48/0.72         <= (~
% 0.48/0.72             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('split', [status(esa)], ['0'])).
% 0.48/0.72  thf('57', plain,
% 0.48/0.72      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.48/0.72         <= (~
% 0.48/0.72             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.48/0.72             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['55', '56'])).
% 0.48/0.72  thf('58', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.48/0.72       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('simplify', [status(thm)], ['57'])).
% 0.48/0.72  thf('59', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.48/0.72       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('split', [status(esa)], ['2'])).
% 0.48/0.72  thf(fc10_tops_1, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.72       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.48/0.72  thf('60', plain,
% 0.48/0.72      (![X7 : $i]:
% 0.48/0.72         ((v3_pre_topc @ (k2_struct_0 @ X7) @ X7)
% 0.48/0.72          | ~ (l1_pre_topc @ X7)
% 0.48/0.72          | ~ (v2_pre_topc @ X7))),
% 0.48/0.72      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.48/0.72  thf(d3_struct_0, axiom,
% 0.48/0.72    (![A:$i]:
% 0.48/0.72     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.48/0.72  thf('61', plain,
% 0.48/0.72      (![X3 : $i]:
% 0.48/0.72         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.48/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.48/0.72  thf(dt_k2_subset_1, axiom,
% 0.48/0.72    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.72  thf('62', plain,
% 0.48/0.72      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.48/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.72  thf('63', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.48/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.72  thf('64', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('65', plain,
% 0.48/0.72      (![X4 : $i, X5 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.48/0.72          | ~ (v3_pre_topc @ X4 @ X5)
% 0.48/0.72          | (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.48/0.72          | ~ (l1_pre_topc @ X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.48/0.72  thf('66', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X0)
% 0.48/0.72          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.48/0.72          | ~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['64', '65'])).
% 0.48/0.72  thf('67', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.48/0.72          | ~ (l1_pre_topc @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['61', '66'])).
% 0.48/0.72  thf('68', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.48/0.72          | ~ (l1_struct_0 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['60', '67'])).
% 0.48/0.72  thf('69', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_struct_0 @ X0)
% 0.48/0.72          | (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['68'])).
% 0.48/0.72  thf('70', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('71', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.48/0.72          | ~ (r2_hidden @ X10 @ (u1_pre_topc @ X11))
% 0.48/0.72          | ((u1_pre_topc @ X11) = (k5_tmap_1 @ X11 @ X10))
% 0.48/0.72          | ~ (l1_pre_topc @ X11)
% 0.48/0.72          | ~ (v2_pre_topc @ X11)
% 0.48/0.72          | (v2_struct_0 @ X11))),
% 0.48/0.72      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.48/0.72  thf('72', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.48/0.72  thf('73', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['69', '72'])).
% 0.48/0.72  thf('74', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['73'])).
% 0.48/0.72  thf('75', plain,
% 0.48/0.72      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('split', [status(esa)], ['2'])).
% 0.48/0.72  thf('76', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ((u1_pre_topc @ X0) = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['73'])).
% 0.48/0.72  thf('77', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('78', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.48/0.72          | ((u1_pre_topc @ (k6_tmap_1 @ X13 @ X12)) = (k5_tmap_1 @ X13 @ X12))
% 0.48/0.72          | ~ (l1_pre_topc @ X13)
% 0.48/0.72          | ~ (v2_pre_topc @ X13)
% 0.48/0.72          | (v2_struct_0 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.48/0.72  thf('79', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['77', '78'])).
% 0.48/0.72  thf('80', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('81', plain,
% 0.48/0.72      (![X8 : $i, X9 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X8)
% 0.48/0.72          | ~ (v2_pre_topc @ X8)
% 0.48/0.72          | (v2_struct_0 @ X8)
% 0.48/0.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.48/0.72          | (v1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.48/0.72  thf('82', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.48/0.72  thf('83', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('84', plain,
% 0.48/0.72      (![X8 : $i, X9 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X8)
% 0.48/0.72          | ~ (v2_pre_topc @ X8)
% 0.48/0.72          | (v2_struct_0 @ X8)
% 0.48/0.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.48/0.72          | (l1_pre_topc @ (k6_tmap_1 @ X8 @ X9)))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.48/0.72  thf('85', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0))),
% 0.48/0.72      inference('sup-', [status(thm)], ['83', '84'])).
% 0.48/0.72  thf('86', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 0.48/0.72      inference('demod', [status(thm)], ['62', '63'])).
% 0.48/0.72  thf('87', plain,
% 0.48/0.72      (![X12 : $i, X13 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.48/0.72          | ((u1_struct_0 @ (k6_tmap_1 @ X13 @ X12)) = (u1_struct_0 @ X13))
% 0.48/0.72          | ~ (l1_pre_topc @ X13)
% 0.48/0.72          | ~ (v2_pre_topc @ X13)
% 0.48/0.72          | (v2_struct_0 @ X13))),
% 0.48/0.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.48/0.72  thf('88', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72              = (u1_struct_0 @ X0)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['86', '87'])).
% 0.48/0.72  thf('89', plain,
% 0.48/0.72      (![X2 : $i]:
% 0.48/0.72         (~ (v1_pre_topc @ X2)
% 0.48/0.72          | ((X2) = (g1_pre_topc @ (u1_struct_0 @ X2) @ (u1_pre_topc @ X2)))
% 0.48/0.72          | ~ (l1_pre_topc @ X2))),
% 0.48/0.72      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.48/0.72  thf('90', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.48/0.72      inference('sup+', [status(thm)], ['88', '89'])).
% 0.48/0.72  thf('91', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['85', '90'])).
% 0.48/0.72  thf('92', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.48/0.72          | ~ (v1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['91'])).
% 0.48/0.72  thf('93', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72                 (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['82', '92'])).
% 0.48/0.72  thf('94', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72               (u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0))),
% 0.48/0.72      inference('simplify', [status(thm)], ['93'])).
% 0.48/0.72  thf('95', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72            = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72               (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['79', '94'])).
% 0.48/0.72  thf('96', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72              = (g1_pre_topc @ (u1_struct_0 @ X0) @ 
% 0.48/0.72                 (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0)))))),
% 0.48/0.72      inference('simplify', [status(thm)], ['95'])).
% 0.48/0.72  thf('97', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         (((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | (v2_struct_0 @ X0))),
% 0.48/0.72      inference('sup+', [status(thm)], ['76', '96'])).
% 0.48/0.72  thf('98', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_struct_0 @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ((k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.72              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.48/0.72      inference('simplify', [status(thm)], ['97'])).
% 0.48/0.72  thf('99', plain,
% 0.48/0.72      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72         | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72         | ~ (l1_struct_0 @ sk_A)
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('sup+', [status(thm)], ['75', '98'])).
% 0.48/0.72  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf(dt_l1_pre_topc, axiom,
% 0.48/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.48/0.72  thf('103', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.48/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.72  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.72      inference('sup-', [status(thm)], ['102', '103'])).
% 0.48/0.72  thf('105', plain,
% 0.48/0.72      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('demod', [status(thm)], ['99', '100', '101', '104'])).
% 0.48/0.72  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('107', plain,
% 0.48/0.72      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('clc', [status(thm)], ['105', '106'])).
% 0.48/0.72  thf('108', plain,
% 0.48/0.72      (![X0 : $i]:
% 0.48/0.72         ((v2_struct_0 @ X0)
% 0.48/0.72          | ~ (v2_pre_topc @ X0)
% 0.48/0.72          | ~ (l1_pre_topc @ X0)
% 0.48/0.72          | ((u1_pre_topc @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.48/0.72              = (k5_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['77', '78'])).
% 0.48/0.72  thf('109', plain,
% 0.48/0.72      (((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72           = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.48/0.72         | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('sup+', [status(thm)], ['107', '108'])).
% 0.48/0.72  thf('110', plain,
% 0.48/0.72      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.48/0.72      inference('clc', [status(thm)], ['51', '52'])).
% 0.48/0.72  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('113', plain,
% 0.48/0.72      (((((k5_tmap_1 @ sk_A @ sk_B) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 0.48/0.72  thf('114', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('115', plain,
% 0.48/0.72      ((((k5_tmap_1 @ sk_A @ sk_B) = (k5_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('clc', [status(thm)], ['113', '114'])).
% 0.48/0.72  thf('116', plain,
% 0.48/0.72      (((((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ sk_A))
% 0.48/0.72         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72         | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72         | ~ (l1_struct_0 @ sk_A)
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('sup+', [status(thm)], ['74', '115'])).
% 0.48/0.72  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.72      inference('sup-', [status(thm)], ['102', '103'])).
% 0.48/0.72  thf('120', plain,
% 0.48/0.72      (((((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ sk_A))
% 0.48/0.72         | (v2_struct_0 @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('demod', [status(thm)], ['116', '117', '118', '119'])).
% 0.48/0.72  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('122', plain,
% 0.48/0.72      ((((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('clc', [status(thm)], ['120', '121'])).
% 0.48/0.72  thf('123', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('124', plain,
% 0.48/0.72      (![X10 : $i, X11 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.48/0.72          | ((u1_pre_topc @ X11) != (k5_tmap_1 @ X11 @ X10))
% 0.48/0.72          | (r2_hidden @ X10 @ (u1_pre_topc @ X11))
% 0.48/0.72          | ~ (l1_pre_topc @ X11)
% 0.48/0.72          | ~ (v2_pre_topc @ X11)
% 0.48/0.72          | (v2_struct_0 @ X11))),
% 0.48/0.72      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.48/0.72  thf('125', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.72        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.48/0.72        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['123', '124'])).
% 0.48/0.72  thf('126', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('128', plain,
% 0.48/0.72      (((v2_struct_0 @ sk_A)
% 0.48/0.72        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.48/0.72        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.48/0.72      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.48/0.72  thf('129', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('130', plain,
% 0.48/0.72      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.48/0.72        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.48/0.72      inference('clc', [status(thm)], ['128', '129'])).
% 0.48/0.72  thf('131', plain,
% 0.48/0.72      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.48/0.72         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['122', '130'])).
% 0.48/0.72  thf('132', plain,
% 0.48/0.72      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('simplify', [status(thm)], ['131'])).
% 0.48/0.72  thf('133', plain,
% 0.48/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('134', plain,
% 0.48/0.72      (![X4 : $i, X5 : $i]:
% 0.48/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.48/0.72          | ~ (r2_hidden @ X4 @ (u1_pre_topc @ X5))
% 0.48/0.72          | (v3_pre_topc @ X4 @ X5)
% 0.48/0.72          | ~ (l1_pre_topc @ X5))),
% 0.48/0.72      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.48/0.72  thf('135', plain,
% 0.48/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.72        | (v3_pre_topc @ sk_B @ sk_A)
% 0.48/0.72        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.48/0.72      inference('sup-', [status(thm)], ['133', '134'])).
% 0.48/0.72  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.72  thf('137', plain,
% 0.48/0.72      (((v3_pre_topc @ sk_B @ sk_A)
% 0.48/0.72        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.48/0.72      inference('demod', [status(thm)], ['135', '136'])).
% 0.48/0.72  thf('138', plain,
% 0.48/0.72      (((v3_pre_topc @ sk_B @ sk_A))
% 0.48/0.72         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.48/0.72      inference('sup-', [status(thm)], ['132', '137'])).
% 0.48/0.72  thf('139', plain,
% 0.48/0.72      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.48/0.72      inference('split', [status(esa)], ['0'])).
% 0.48/0.72  thf('140', plain,
% 0.48/0.72      (~
% 0.48/0.72       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.48/0.72          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.48/0.72       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.48/0.72      inference('sup-', [status(thm)], ['138', '139'])).
% 0.48/0.72  thf('141', plain, ($false),
% 0.48/0.72      inference('sat_resolution*', [status(thm)], ['1', '58', '59', '140'])).
% 0.48/0.72  
% 0.48/0.72  % SZS output end Refutation
% 0.48/0.72  
% 0.48/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
