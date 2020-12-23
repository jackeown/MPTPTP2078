%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HzqcrNz7oT

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:47 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 539 expanded)
%              Number of leaves         :   27 ( 160 expanded)
%              Depth                    :   20
%              Number of atoms          : 1896 (8145 expanded)
%              Number of equality atoms :   86 ( 345 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ( ( u1_pre_topc @ X16 )
        = ( k5_tmap_1 @ X16 @ X15 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k6_tmap_1 @ X12 @ X11 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X12 ) @ ( k5_tmap_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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

thf('32',plain,(
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

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( k5_tmap_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
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

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('44',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X18 @ X17 ) )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','58'])).

thf('60',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_tops_2 @ X8 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) ) )
      | ( v1_tops_2 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_tops_2 @ X0 @ sk_A )
        | ~ ( v1_tops_2 @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66'])).

thf('68',plain,
    ( ( ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('70',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( r1_tarski @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['69','76'])).

thf('78',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('79',plain,(
    v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','58'])).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_tarski @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( ( u1_pre_topc @ sk_A )
        = ( k5_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('93',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('94',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_tops_2 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_tops_2 @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ X0 ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','100'])).

thf('102',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('103',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('104',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('105',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('113',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_tops_2 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) ) )
      | ( v1_tops_2 @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t32_compts_1])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('126',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( r1_tarski @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v1_tops_2 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('127',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('130',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','123','124','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','133'])).

thf('135',plain,
    ( ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_pre_topc @ X16 )
       != ( k5_tmap_1 @ X16 @ X15 ) )
      | ( r2_hidden @ X15 @ ( u1_pre_topc @ X16 ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( u1_pre_topc @ sk_A )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( ( u1_pre_topc @ sk_A )
       != ( u1_pre_topc @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['135','143'])).

thf('145',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X4 ) )
      | ( v3_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('148',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('153',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','30','31','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HzqcrNz7oT
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 149 iterations in 0.108s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.38/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.56  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.38/0.56  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.38/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.38/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.56  thf(t106_tmap_1, conjecture,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.56             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.38/0.56               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i]:
% 0.38/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56            ( l1_pre_topc @ A ) ) =>
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56              ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.56                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.38/0.56                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (~
% 0.38/0.56       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.38/0.56       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d5_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( v3_pre_topc @ B @ A ) <=>
% 0.38/0.56             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.38/0.56          | ~ (v3_pre_topc @ X3 @ X4)
% 0.38/0.56          | (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.38/0.56          | ~ (l1_pre_topc @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.38/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.38/0.56        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.38/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t103_tmap_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.38/0.56             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.56          | ~ (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.38/0.56          | ((u1_pre_topc @ X16) = (k5_tmap_1 @ X16 @ X15))
% 0.38/0.56          | ~ (l1_pre_topc @ X16)
% 0.38/0.56          | ~ (v2_pre_topc @ X16)
% 0.38/0.56          | (v2_struct_0 @ X16))),
% 0.38/0.56      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.38/0.56  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.38/0.56        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('clc', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d9_tmap_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( k6_tmap_1 @ A @ B ) =
% 0.38/0.56             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.56          | ((k6_tmap_1 @ X12 @ X11)
% 0.38/0.56              = (g1_pre_topc @ (u1_struct_0 @ X12) @ (k5_tmap_1 @ X12 @ X11)))
% 0.38/0.56          | ~ (l1_pre_topc @ X12)
% 0.38/0.56          | ~ (v2_pre_topc @ X12)
% 0.38/0.56          | (v2_struct_0 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.38/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.38/0.56            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.38/0.56  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.38/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('clc', [status(thm)], ['24', '25'])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      ((((k6_tmap_1 @ sk_A @ sk_B)
% 0.38/0.56          = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.38/0.56         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['18', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((((k6_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= (~
% 0.38/0.56             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))) & 
% 0.38/0.56             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.38/0.56       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('simplify', [status(thm)], ['29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.38/0.56       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t104_tmap_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.56           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.38/0.56             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.56          | ((u1_pre_topc @ (k6_tmap_1 @ X18 @ X17)) = (k5_tmap_1 @ X18 @ X17))
% 0.38/0.56          | ~ (l1_pre_topc @ X18)
% 0.38/0.56          | ~ (v2_pre_topc @ X18)
% 0.38/0.56          | (v2_struct_0 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.38/0.56  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf(dt_u1_pre_topc, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( m1_subset_1 @
% 0.38/0.56         ( u1_pre_topc @ A ) @ 
% 0.38/0.56         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (![X5 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.38/0.56          | ~ (l1_pre_topc @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.56         (k1_zfmisc_1 @ 
% 0.38/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.38/0.56        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_k6_tmap_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.56         ( l1_pre_topc @ A ) & 
% 0.38/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.38/0.56         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.38/0.56         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X13)
% 0.38/0.56          | ~ (v2_pre_topc @ X13)
% 0.38/0.56          | (v2_struct_0 @ X13)
% 0.38/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.38/0.56          | (l1_pre_topc @ (k6_tmap_1 @ X13 @ X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | (v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.56  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.38/0.56  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('49', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X17 : $i, X18 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.56          | ((u1_struct_0 @ (k6_tmap_1 @ X18 @ X17)) = (u1_struct_0 @ X18))
% 0.38/0.56          | ~ (l1_pre_topc @ X18)
% 0.38/0.56          | ~ (v2_pre_topc @ X18)
% 0.38/0.56          | (v2_struct_0 @ X18))),
% 0.38/0.56      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.56  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (((v2_struct_0 @ sk_A)
% 0.38/0.56        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.56  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '58'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf(t32_compts_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( v1_tops_2 @ B @ A ) & 
% 0.38/0.56             ( m1_subset_1 @
% 0.38/0.56               B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) <=>
% 0.38/0.56           ( ( v1_tops_2 @
% 0.38/0.56               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.38/0.56             ( m1_subset_1 @
% 0.38/0.56               B @ 
% 0.38/0.56               ( k1_zfmisc_1 @
% 0.38/0.56                 ( k1_zfmisc_1 @
% 0.38/0.56                   ( u1_struct_0 @
% 0.38/0.56                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ X8 @ 
% 0.38/0.56             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k1_zfmisc_1 @ 
% 0.38/0.56                 (u1_struct_0 @ 
% 0.38/0.56                  (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))))))
% 0.38/0.56          | (v1_tops_2 @ X8 @ X9)
% 0.38/0.56          | ~ (l1_pre_topc @ X9)
% 0.38/0.56          | ~ (v2_pre_topc @ X9)
% 0.38/0.56          | (v2_struct_0 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (~ (m1_subset_1 @ X0 @ 
% 0.38/0.56              (k1_zfmisc_1 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.38/0.56           | (v2_struct_0 @ sk_A)
% 0.38/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.38/0.56           | (v1_tops_2 @ X0 @ sk_A)
% 0.38/0.56           | ~ (v1_tops_2 @ X0 @ 
% 0.38/0.56                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.56  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (~ (m1_subset_1 @ X0 @ 
% 0.38/0.56              (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.56           | (v2_struct_0 @ sk_A)
% 0.38/0.56           | (v1_tops_2 @ X0 @ sk_A)
% 0.38/0.56           | ~ (v1_tops_2 @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('demod', [status(thm)], ['62', '63', '64', '65', '66'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (((~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A)
% 0.38/0.56         | (v2_struct_0 @ sk_A)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['59', '67'])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (![X5 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.38/0.56          | ~ (l1_pre_topc @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.38/0.56  thf(t78_tops_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_pre_topc @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @
% 0.38/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.56           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (r1_tarski @ X6 @ (u1_pre_topc @ X7))
% 0.38/0.56          | (v1_tops_2 @ X6 @ X7)
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.38/0.56          | ~ (r1_tarski @ (u1_pre_topc @ X0) @ (u1_pre_topc @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.56  thf(d10_xboole_0, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.56      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['72', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['75'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['69', '76'])).
% 0.38/0.56  thf('78', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      ((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['77', '78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      ((((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('demod', [status(thm)], ['68', '79'])).
% 0.38/0.56  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (((v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('clc', [status(thm)], ['80', '81'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '58'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (v1_tops_2 @ X6 @ X7)
% 0.38/0.56          | (r1_tarski @ X6 @ (u1_pre_topc @ X7))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.56        | (r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.38/0.56        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.56  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.38/0.56        | ~ (v1_tops_2 @ (k5_tmap_1 @ sk_A @ sk_B) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (((r1_tarski @ (k5_tmap_1 @ sk_A @ sk_B) @ (u1_pre_topc @ sk_A)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['82', '87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X0 : $i, X2 : $i]:
% 0.38/0.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_tops_2 @ (u1_pre_topc @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['75'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (![X5 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.38/0.56          | ~ (l1_pre_topc @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ X10 @ X9)
% 0.38/0.56          | ~ (m1_subset_1 @ X10 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.38/0.56          | (m1_subset_1 @ X10 @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k1_zfmisc_1 @ 
% 0.38/0.56               (u1_struct_0 @ 
% 0.38/0.56                (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9))))))
% 0.38/0.56          | ~ (l1_pre_topc @ X9)
% 0.38/0.56          | ~ (v2_pre_topc @ X9)
% 0.38/0.56          | (v2_struct_0 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k1_zfmisc_1 @ 
% 0.38/0.56               (u1_struct_0 @ 
% 0.38/0.56                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.38/0.56          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['93', '94'])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_tops_2 @ (u1_pre_topc @ X0) @ X0)
% 0.38/0.56          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k1_zfmisc_1 @ 
% 0.38/0.56               (u1_struct_0 @ 
% 0.38/0.56                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56             (k1_zfmisc_1 @ 
% 0.38/0.56              (k1_zfmisc_1 @ 
% 0.38/0.56               (u1_struct_0 @ 
% 0.38/0.56                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['92', '96'])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56           (k1_zfmisc_1 @ 
% 0.38/0.56            (k1_zfmisc_1 @ 
% 0.38/0.56             (u1_struct_0 @ 
% 0.38/0.56              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['97'])).
% 0.38/0.56  thf('99', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X6 @ 
% 0.38/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.56          | ~ (v1_tops_2 @ X6 @ X7)
% 0.38/0.56          | (r1_tarski @ X6 @ (u1_pre_topc @ X7))
% 0.38/0.56          | ~ (l1_pre_topc @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (l1_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | ~ (l1_pre_topc @ 
% 0.38/0.56               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.38/0.56          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.38/0.56             (u1_pre_topc @ 
% 0.38/0.56              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))
% 0.38/0.56          | ~ (v1_tops_2 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.38/0.56  thf('101', plain,
% 0.38/0.56      (((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | (r1_tarski @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.56            (u1_pre_topc @ 
% 0.38/0.56             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.38/0.56         | ~ (l1_pre_topc @ 
% 0.38/0.56              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.38/0.56         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.56         | (v2_struct_0 @ sk_A)
% 0.38/0.56         | ~ (l1_pre_topc @ sk_A)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['91', '100'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('103', plain,
% 0.38/0.56      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('105', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('108', plain,
% 0.38/0.56      (((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | (r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | (v2_struct_0 @ sk_A)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('demod', [status(thm)],
% 0.38/0.56                ['101', '102', '103', '104', '105', '106', '107'])).
% 0.38/0.56  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('110', plain,
% 0.38/0.56      ((((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.56         | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('clc', [status(thm)], ['108', '109'])).
% 0.38/0.56  thf('111', plain,
% 0.38/0.56      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.56         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.56                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('split', [status(esa)], ['2'])).
% 0.38/0.56  thf('112', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.38/0.56           (k1_zfmisc_1 @ 
% 0.38/0.56            (k1_zfmisc_1 @ 
% 0.38/0.56             (u1_struct_0 @ 
% 0.38/0.56              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))))
% 0.38/0.56          | ~ (v2_pre_topc @ X0)
% 0.38/0.56          | (v2_struct_0 @ X0)
% 0.38/0.57          | ~ (l1_pre_topc @ X0))),
% 0.38/0.57      inference('simplify', [status(thm)], ['97'])).
% 0.38/0.57  thf('113', plain,
% 0.38/0.57      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.57          (k1_zfmisc_1 @ 
% 0.38/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))))
% 0.38/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (v2_pre_topc @ sk_A)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup+', [status(thm)], ['111', '112'])).
% 0.38/0.57  thf('114', plain,
% 0.38/0.57      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('117', plain,
% 0.38/0.57      ((((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.57          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['113', '114', '115', '116'])).
% 0.38/0.57  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('119', plain,
% 0.38/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('clc', [status(thm)], ['117', '118'])).
% 0.38/0.57  thf('120', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (~ (v1_tops_2 @ X10 @ X9)
% 0.38/0.57          | ~ (m1_subset_1 @ X10 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9))))
% 0.38/0.57          | (v1_tops_2 @ X10 @ 
% 0.38/0.57             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 0.38/0.57          | ~ (l1_pre_topc @ X9)
% 0.38/0.57          | ~ (v2_pre_topc @ X9)
% 0.38/0.57          | (v2_struct_0 @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t32_compts_1])).
% 0.38/0.57  thf('121', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.38/0.57         | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['119', '120'])).
% 0.38/0.57  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('124', plain,
% 0.38/0.57      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('split', [status(esa)], ['2'])).
% 0.38/0.57  thf('125', plain,
% 0.38/0.57      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('clc', [status(thm)], ['117', '118'])).
% 0.38/0.57  thf('126', plain,
% 0.38/0.57      (![X6 : $i, X7 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X6 @ 
% 0.38/0.57             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.38/0.57          | ~ (r1_tarski @ X6 @ (u1_pre_topc @ X7))
% 0.38/0.57          | (v1_tops_2 @ X6 @ X7)
% 0.38/0.57          | ~ (l1_pre_topc @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.38/0.57  thf('127', plain,
% 0.38/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.38/0.57         | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['125', '126'])).
% 0.38/0.57  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('129', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.57      inference('simplify', [status(thm)], ['73'])).
% 0.38/0.57  thf('130', plain,
% 0.38/0.57      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.38/0.57  thf('131', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A)
% 0.38/0.57         | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['121', '122', '123', '124', '130'])).
% 0.38/0.57  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('133', plain,
% 0.38/0.57      (((v1_tops_2 @ (u1_pre_topc @ sk_A) @ (k6_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('clc', [status(thm)], ['131', '132'])).
% 0.38/0.57  thf('134', plain,
% 0.38/0.57      (((r1_tarski @ (u1_pre_topc @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['110', '133'])).
% 0.38/0.57  thf('135', plain,
% 0.38/0.57      ((((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('demod', [status(thm)], ['90', '134'])).
% 0.38/0.57  thf('136', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('137', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.57          | ((u1_pre_topc @ X16) != (k5_tmap_1 @ X16 @ X15))
% 0.38/0.57          | (r2_hidden @ X15 @ (u1_pre_topc @ X16))
% 0.38/0.57          | ~ (l1_pre_topc @ X16)
% 0.38/0.57          | ~ (v2_pre_topc @ X16)
% 0.38/0.57          | (v2_struct_0 @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.38/0.57  thf('138', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.38/0.57        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['136', '137'])).
% 0.38/0.57  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('141', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A)
% 0.38/0.57        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.38/0.57        | ((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.38/0.57  thf('142', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('143', plain,
% 0.38/0.57      ((((u1_pre_topc @ sk_A) != (k5_tmap_1 @ sk_A @ sk_B))
% 0.38/0.57        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.38/0.57      inference('clc', [status(thm)], ['141', '142'])).
% 0.38/0.57  thf('144', plain,
% 0.38/0.57      (((((u1_pre_topc @ sk_A) != (u1_pre_topc @ sk_A))
% 0.38/0.57         | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['135', '143'])).
% 0.38/0.57  thf('145', plain,
% 0.38/0.57      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['144'])).
% 0.38/0.57  thf('146', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('147', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.38/0.57          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X4))
% 0.38/0.57          | (v3_pre_topc @ X3 @ X4)
% 0.38/0.57          | ~ (l1_pre_topc @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.38/0.57  thf('148', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['146', '147'])).
% 0.38/0.57  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('150', plain,
% 0.38/0.57      (((v3_pre_topc @ sk_B @ sk_A)
% 0.38/0.57        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['148', '149'])).
% 0.38/0.57  thf('151', plain,
% 0.38/0.57      (((v3_pre_topc @ sk_B @ sk_A))
% 0.38/0.57         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['145', '150'])).
% 0.38/0.57  thf('152', plain,
% 0.38/0.57      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('153', plain,
% 0.38/0.57      (~
% 0.38/0.57       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.38/0.57          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.38/0.57       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['151', '152'])).
% 0.38/0.57  thf('154', plain, ($false),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['1', '30', '31', '153'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
