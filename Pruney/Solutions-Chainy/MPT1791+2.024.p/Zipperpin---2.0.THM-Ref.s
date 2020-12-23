%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DSC42E216K

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:49 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 332 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   18
%              Number of atoms          :  953 (5003 expanded)
%              Number of equality atoms :   41 ( 221 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k6_tmap_1 @ X6 @ X5 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( k5_tmap_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( ( u1_pre_topc @ X12 )
        = ( k5_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t103_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X14 @ X13 ) )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('36',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( u1_pre_topc @ ( k6_tmap_1 @ X14 @ X13 ) )
        = ( k5_tmap_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['42','50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X9 @ ( k5_tmap_1 @ X10 @ X9 ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t102_tmap_1])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ sk_B @ ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(t60_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v3_pre_topc @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v3_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v3_pre_topc @ X2 @ ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X3 ) @ ( u1_pre_topc @ X3 ) ) ) ) )
      | ( v3_pre_topc @ X2 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( v2_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t60_pre_topc])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ( ~ ( v3_pre_topc @ sk_B @ ( k6_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('76',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['22','74','75'])).

thf('77',plain,(
    r2_hidden @ sk_B @ ( u1_pre_topc @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','76'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_pre_topc @ sk_A )
      = ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','12','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','80'])).

thf('82',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('83',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','74'])).

thf('84',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
 != ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DSC42E216K
% 0.17/0.38  % Computer   : n006.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 09:34:23 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 129 iterations in 0.067s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.25/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.55  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.25/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.25/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.55  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.25/0.55  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.25/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.25/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.55  thf(t106_tmap_1, conjecture,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.25/0.55             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.25/0.55               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i]:
% 0.25/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.55            ( l1_pre_topc @ A ) ) =>
% 0.25/0.55          ( ![B:$i]:
% 0.25/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55              ( ( v3_pre_topc @ B @ A ) <=>
% 0.25/0.55                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.25/0.55                  ( k6_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t106_tmap_1])).
% 0.25/0.55  thf('0', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(d9_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( k6_tmap_1 @ A @ B ) =
% 0.25/0.55             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.55  thf('1', plain,
% 0.25/0.55      (![X5 : $i, X6 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.25/0.55          | ((k6_tmap_1 @ X6 @ X5)
% 0.25/0.55              = (g1_pre_topc @ (u1_struct_0 @ X6) @ (k5_tmap_1 @ X6 @ X5)))
% 0.25/0.55          | ~ (l1_pre_topc @ X6)
% 0.25/0.55          | ~ (v2_pre_topc @ X6)
% 0.25/0.55          | (v2_struct_0 @ X6))),
% 0.25/0.55      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.25/0.55  thf('2', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.55  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('5', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.55            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.25/0.55  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('7', plain,
% 0.25/0.55      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('clc', [status(thm)], ['5', '6'])).
% 0.25/0.55  thf('8', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t103_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) <=>
% 0.25/0.55             ( ( u1_pre_topc @ A ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      (![X11 : $i, X12 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.25/0.55          | ~ (r2_hidden @ X11 @ (u1_pre_topc @ X12))
% 0.25/0.55          | ((u1_pre_topc @ X12) = (k5_tmap_1 @ X12 @ X11))
% 0.25/0.55          | ~ (l1_pre_topc @ X12)
% 0.25/0.55          | ~ (v2_pre_topc @ X12)
% 0.25/0.55          | (v2_struct_0 @ X12))),
% 0.25/0.55      inference('cnf', [status(esa)], [t103_tmap_1])).
% 0.25/0.55  thf('10', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55        | ~ (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.55  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('13', plain,
% 0.25/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('14', plain,
% 0.25/0.55      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.25/0.55      inference('split', [status(esa)], ['13'])).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(d5_pre_topc, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( v3_pre_topc @ B @ A ) <=>
% 0.25/0.55             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.25/0.55  thf('16', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.25/0.55          | ~ (v3_pre_topc @ X0 @ X1)
% 0.25/0.55          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.25/0.55          | ~ (l1_pre_topc @ X1))),
% 0.25/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.25/0.55  thf('17', plain,
% 0.25/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | (r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.25/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.25/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('19', plain,
% 0.25/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))
% 0.25/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.25/0.55  thf('20', plain,
% 0.25/0.55      (((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A)))
% 0.25/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['14', '19'])).
% 0.25/0.55  thf('21', plain,
% 0.25/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          != (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (~
% 0.25/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B))) | 
% 0.25/0.55       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('split', [status(esa)], ['21'])).
% 0.25/0.55  thf('23', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('24', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t104_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.25/0.55             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.55  thf('25', plain,
% 0.25/0.55      (![X13 : $i, X14 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.55          | ((u1_struct_0 @ (k6_tmap_1 @ X14 @ X13)) = (u1_struct_0 @ X14))
% 0.25/0.55          | ~ (l1_pre_topc @ X14)
% 0.25/0.55          | ~ (v2_pre_topc @ X14)
% 0.25/0.55          | (v2_struct_0 @ X14))),
% 0.25/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.25/0.55  thf('26', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.55  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('29', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.25/0.55  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('31', plain,
% 0.25/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('clc', [status(thm)], ['29', '30'])).
% 0.25/0.55  thf('32', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.25/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.25/0.55          | (v3_pre_topc @ X0 @ X1)
% 0.25/0.55          | ~ (l1_pre_topc @ X1))),
% 0.25/0.55      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.25/0.55  thf('33', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55          | (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.25/0.55  thf('34', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(dt_k6_tmap_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.55         ( l1_pre_topc @ A ) & 
% 0.25/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.55       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.25/0.55         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.25/0.55         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.25/0.55  thf('35', plain,
% 0.25/0.55      (![X7 : $i, X8 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ X7)
% 0.25/0.55          | ~ (v2_pre_topc @ X7)
% 0.25/0.55          | (v2_struct_0 @ X7)
% 0.25/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.25/0.55          | (l1_pre_topc @ (k6_tmap_1 @ X7 @ X8)))),
% 0.25/0.55      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.25/0.55  thf('36', plain,
% 0.25/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55        | (v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.25/0.55  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('39', plain,
% 0.25/0.55      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.25/0.55  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('41', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.25/0.55  thf('42', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['33', '41'])).
% 0.25/0.55  thf('43', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('44', plain,
% 0.25/0.55      (![X13 : $i, X14 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.25/0.55          | ((u1_pre_topc @ (k6_tmap_1 @ X14 @ X13)) = (k5_tmap_1 @ X14 @ X13))
% 0.25/0.55          | ~ (l1_pre_topc @ X14)
% 0.25/0.55          | ~ (v2_pre_topc @ X14)
% 0.25/0.55          | (v2_struct_0 @ X14))),
% 0.25/0.55      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.25/0.55  thf('45', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.25/0.55  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('48', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55            = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.25/0.55  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('50', plain,
% 0.25/0.55      (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['48', '49'])).
% 0.25/0.55  thf('51', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55          | ~ (r2_hidden @ X0 @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['42', '50'])).
% 0.25/0.55  thf('52', plain,
% 0.25/0.55      ((~ (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55        | (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['23', '51'])).
% 0.25/0.55  thf('53', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t102_tmap_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( r2_hidden @ B @ ( k5_tmap_1 @ A @ B ) ) ) ) ))).
% 0.25/0.55  thf('54', plain,
% 0.25/0.55      (![X9 : $i, X10 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.25/0.55          | (r2_hidden @ X9 @ (k5_tmap_1 @ X10 @ X9))
% 0.25/0.55          | ~ (l1_pre_topc @ X10)
% 0.25/0.55          | ~ (v2_pre_topc @ X10)
% 0.25/0.55          | (v2_struct_0 @ X10))),
% 0.25/0.55      inference('cnf', [status(esa)], [t102_tmap_1])).
% 0.25/0.55  thf('55', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55        | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.25/0.55  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('58', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A) | (r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.25/0.55  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('60', plain, ((r2_hidden @ sk_B @ (k5_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['58', '59'])).
% 0.25/0.55  thf('61', plain, ((v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('demod', [status(thm)], ['52', '60'])).
% 0.25/0.55  thf('62', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('63', plain,
% 0.25/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['13'])).
% 0.25/0.55  thf(t60_pre_topc, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( ( v3_pre_topc @ B @ A ) & 
% 0.25/0.55             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.25/0.55           ( ( v3_pre_topc @
% 0.25/0.55               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.25/0.55             ( m1_subset_1 @
% 0.25/0.55               B @ 
% 0.25/0.55               ( k1_zfmisc_1 @
% 0.25/0.55                 ( u1_struct_0 @
% 0.25/0.55                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('64', plain,
% 0.25/0.55      (![X2 : $i, X3 : $i]:
% 0.25/0.55         (~ (v3_pre_topc @ X2 @ 
% 0.25/0.55             (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))
% 0.25/0.55          | ~ (m1_subset_1 @ X2 @ 
% 0.25/0.55               (k1_zfmisc_1 @ 
% 0.25/0.55                (u1_struct_0 @ 
% 0.25/0.55                 (g1_pre_topc @ (u1_struct_0 @ X3) @ (u1_pre_topc @ X3)))))
% 0.25/0.55          | (v3_pre_topc @ X2 @ X3)
% 0.25/0.55          | ~ (l1_pre_topc @ X3)
% 0.25/0.55          | ~ (v2_pre_topc @ X3))),
% 0.25/0.55      inference('cnf', [status(esa)], [t60_pre_topc])).
% 0.25/0.55  thf('65', plain,
% 0.25/0.55      ((![X0 : $i]:
% 0.25/0.55          (~ (m1_subset_1 @ X0 @ 
% 0.25/0.55              (k1_zfmisc_1 @ (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.25/0.55           | ~ (v2_pre_topc @ sk_A)
% 0.25/0.55           | ~ (l1_pre_topc @ sk_A)
% 0.25/0.55           | (v3_pre_topc @ X0 @ sk_A)
% 0.25/0.55           | ~ (v3_pre_topc @ X0 @ 
% 0.25/0.55                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.25/0.55  thf('66', plain,
% 0.25/0.55      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.25/0.55      inference('clc', [status(thm)], ['29', '30'])).
% 0.25/0.55  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('69', plain,
% 0.25/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['13'])).
% 0.25/0.55  thf('70', plain,
% 0.25/0.55      ((![X0 : $i]:
% 0.25/0.55          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55           | (v3_pre_topc @ X0 @ sk_A)
% 0.25/0.55           | ~ (v3_pre_topc @ X0 @ (k6_tmap_1 @ sk_A @ sk_B))))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.25/0.55  thf('71', plain,
% 0.25/0.55      (((~ (v3_pre_topc @ sk_B @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.55         | (v3_pre_topc @ sk_B @ sk_A)))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['62', '70'])).
% 0.25/0.55  thf('72', plain,
% 0.25/0.55      (((v3_pre_topc @ sk_B @ sk_A))
% 0.25/0.55         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['61', '71'])).
% 0.25/0.55  thf('73', plain,
% 0.25/0.55      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.25/0.55      inference('split', [status(esa)], ['21'])).
% 0.25/0.55  thf('74', plain,
% 0.25/0.55      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.25/0.55       ~
% 0.25/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.25/0.55  thf('75', plain,
% 0.25/0.55      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.25/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('split', [status(esa)], ['13'])).
% 0.25/0.55  thf('76', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 0.25/0.55      inference('sat_resolution*', [status(thm)], ['22', '74', '75'])).
% 0.25/0.55  thf('77', plain, ((r2_hidden @ sk_B @ (u1_pre_topc @ sk_A))),
% 0.25/0.55      inference('simpl_trail', [status(thm)], ['20', '76'])).
% 0.25/0.55  thf('78', plain,
% 0.25/0.55      (((v2_struct_0 @ sk_A)
% 0.25/0.55        | ((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['10', '11', '12', '77'])).
% 0.25/0.55  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('80', plain, (((u1_pre_topc @ sk_A) = (k5_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('clc', [status(thm)], ['78', '79'])).
% 0.25/0.55  thf('81', plain,
% 0.25/0.55      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.55         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['7', '80'])).
% 0.25/0.55  thf('82', plain,
% 0.25/0.55      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          != (k6_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.55         <= (~
% 0.25/0.55             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55                = (k6_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.55      inference('split', [status(esa)], ['21'])).
% 0.25/0.55  thf('83', plain,
% 0.25/0.55      (~
% 0.25/0.55       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55          = (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.55      inference('sat_resolution*', [status(thm)], ['22', '74'])).
% 0.25/0.55  thf('84', plain,
% 0.25/0.55      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.25/0.55         != (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.55      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.25/0.55  thf('85', plain, ($false),
% 0.25/0.55      inference('simplify_reflect-', [status(thm)], ['81', '84'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
