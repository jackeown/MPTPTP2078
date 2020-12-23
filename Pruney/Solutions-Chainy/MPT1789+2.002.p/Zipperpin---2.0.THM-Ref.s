%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kn6jmJqJmD

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:44 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 251 expanded)
%              Number of leaves         :   19 (  80 expanded)
%              Depth                    :   13
%              Number of atoms          :  726 (4016 expanded)
%              Number of equality atoms :   51 ( 279 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t104_tmap_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
                = ( u1_struct_0 @ A ) )
              & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
                = ( k5_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_tmap_1])).

thf('0',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k5_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k5_tmap_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_tmap_1])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_tmap_1 @ sk_A @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != ( g1_pre_topc @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( k5_tmap_1 @ sk_A @ sk_B )
        = ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
      = ( u1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k6_tmap_1 @ X6 @ X5 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X6 ) @ ( k5_tmap_1 @ X6 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_tmap_1])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_tmap_1 @ sk_A @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v1_pre_topc @ ( k6_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('26',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( l1_pre_topc @ ( k6_tmap_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_tmap_1])).

thf('35',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k5_tmap_1 @ sk_A @ sk_B )
    = ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','22','23','31','32','40'])).

thf('42',plain,
    ( ( ( k5_tmap_1 @ sk_A @ sk_B )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','41'])).

thf('43',plain,
    ( $false
   <= ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('45',plain,(
    m1_subset_1 @ ( k5_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_pre_topc @ X3 @ X4 )
       != ( g1_pre_topc @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) )
       != X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('51',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('52',plain,(
    v1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('53',plain,
    ( ( k6_tmap_1 @ sk_A @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( k5_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('54',plain,(
    l1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53','54'])).

thf('56',plain,
    ( ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
   <= ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( k5_tmap_1 @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ sk_B ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    ( u1_pre_topc @ ( k6_tmap_1 @ sk_A @ sk_B ) )
 != ( k5_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['43','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Kn6jmJqJmD
% 0.15/0.38  % Computer   : n014.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 12:45:52 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 26 iterations in 0.018s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.25/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.25/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.51  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.25/0.51  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.25/0.51  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.25/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.51  thf(t104_tmap_1, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.25/0.51             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.51            ( l1_pre_topc @ A ) ) =>
% 0.25/0.51          ( ![B:$i]:
% 0.25/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51              ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.25/0.51                ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) =
% 0.25/0.51                  ( k5_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t104_tmap_1])).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A))
% 0.25/0.51        | ((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51            != (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      ((((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.51         <= (~
% 0.25/0.51             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('split', [status(esa)], ['0'])).
% 0.25/0.51  thf(abstractness_v1_pre_topc, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( l1_pre_topc @ A ) =>
% 0.25/0.51       ( ( v1_pre_topc @ A ) =>
% 0.25/0.51         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v1_pre_topc @ X0)
% 0.25/0.51          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.51          | ~ (l1_pre_topc @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.25/0.51  thf('3', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(dt_k5_tmap_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.51         ( l1_pre_topc @ A ) & 
% 0.25/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.51       ( m1_subset_1 @
% 0.25/0.51         ( k5_tmap_1 @ A @ B ) @ 
% 0.25/0.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X7)
% 0.25/0.51          | ~ (v2_pre_topc @ X7)
% 0.25/0.51          | (v2_struct_0 @ X7)
% 0.25/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.25/0.51          | (m1_subset_1 @ (k5_tmap_1 @ X7 @ X8) @ 
% 0.25/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))))),
% 0.25/0.51      inference('cnf', [status(esa)], [dt_k5_tmap_1])).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.25/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.25/0.51        | (v2_struct_0 @ sk_A)
% 0.25/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.25/0.51  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.25/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.25/0.51        | (v2_struct_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.25/0.51  thf('9', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.25/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.25/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.25/0.51  thf(free_g1_pre_topc, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.25/0.51       ( ![C:$i,D:$i]:
% 0.25/0.51         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.25/0.51           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.51         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.25/0.51          | ((X4) = (X2))
% 0.25/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.25/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (((k5_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.25/0.51          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51              != (g1_pre_topc @ X1 @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.25/0.51  thf('13', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51            != (X0))
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ~ (v1_pre_topc @ X0)
% 0.25/0.51          | ((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['2', '12'])).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      ((((k5_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51          = (u1_pre_topc @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.25/0.51        | ~ (v1_pre_topc @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.51        | ~ (l1_pre_topc @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(d9_tmap_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.25/0.51       ( ![B:$i]:
% 0.25/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.51           ( ( k6_tmap_1 @ A @ B ) =
% 0.25/0.51             ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      (![X5 : $i, X6 : $i]:
% 0.25/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.25/0.51          | ((k6_tmap_1 @ X6 @ X5)
% 0.25/0.51              = (g1_pre_topc @ (u1_struct_0 @ X6) @ (k5_tmap_1 @ X6 @ X5)))
% 0.25/0.51          | ~ (l1_pre_topc @ X6)
% 0.25/0.51          | ~ (v2_pre_topc @ X6)
% 0.25/0.51          | (v2_struct_0 @ X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [d9_tmap_1])).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (((v2_struct_0 @ sk_A)
% 0.25/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.25/0.51        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.25/0.51  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('20', plain,
% 0.25/0.51      (((v2_struct_0 @ sk_A)
% 0.25/0.51        | ((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51            = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.25/0.51  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('22', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(dt_k6_tmap_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.25/0.51         ( l1_pre_topc @ A ) & 
% 0.25/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.25/0.51       ( ( v1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.25/0.51         ( v2_pre_topc @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.25/0.51         ( l1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) ) ))).
% 0.25/0.51  thf('25', plain,
% 0.25/0.51      (![X9 : $i, X10 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X9)
% 0.25/0.51          | ~ (v2_pre_topc @ X9)
% 0.25/0.51          | (v2_struct_0 @ X9)
% 0.25/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.51          | (v1_pre_topc @ (k6_tmap_1 @ X9 @ X10)))),
% 0.25/0.51      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.25/0.51  thf('26', plain,
% 0.25/0.51      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51        | (v2_struct_0 @ sk_A)
% 0.25/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.25/0.51  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('29', plain,
% 0.25/0.51      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.25/0.51  thf('30', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('31', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.25/0.51  thf('32', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('33', plain,
% 0.25/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('34', plain,
% 0.25/0.51      (![X9 : $i, X10 : $i]:
% 0.25/0.51         (~ (l1_pre_topc @ X9)
% 0.25/0.51          | ~ (v2_pre_topc @ X9)
% 0.25/0.51          | (v2_struct_0 @ X9)
% 0.25/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.25/0.51          | (l1_pre_topc @ (k6_tmap_1 @ X9 @ X10)))),
% 0.25/0.51      inference('cnf', [status(esa)], [dt_k6_tmap_1])).
% 0.25/0.51  thf('35', plain,
% 0.25/0.51      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51        | (v2_struct_0 @ sk_A)
% 0.25/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.25/0.51        | ~ (l1_pre_topc @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.25/0.51  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('38', plain,
% 0.25/0.51      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.25/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.25/0.51  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('40', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.25/0.51  thf('41', plain,
% 0.25/0.51      (((k5_tmap_1 @ sk_A @ sk_B) = (u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('demod', [status(thm)], ['14', '22', '23', '31', '32', '40'])).
% 0.25/0.51  thf('42', plain,
% 0.25/0.51      ((((k5_tmap_1 @ sk_A @ sk_B) != (k5_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.51         <= (~
% 0.25/0.51             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('demod', [status(thm)], ['1', '41'])).
% 0.25/0.51  thf('43', plain,
% 0.25/0.51      (($false)
% 0.25/0.51         <= (~
% 0.25/0.51             (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51                = (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('simplify', [status(thm)], ['42'])).
% 0.25/0.51  thf('44', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (~ (v1_pre_topc @ X0)
% 0.25/0.51          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.25/0.51          | ~ (l1_pre_topc @ X0))),
% 0.25/0.51      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.25/0.51  thf('45', plain,
% 0.25/0.51      ((m1_subset_1 @ (k5_tmap_1 @ sk_A @ sk_B) @ 
% 0.25/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.25/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.25/0.51  thf('46', plain,
% 0.25/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.25/0.51         (((g1_pre_topc @ X3 @ X4) != (g1_pre_topc @ X1 @ X2))
% 0.25/0.51          | ((X3) = (X1))
% 0.25/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.25/0.51      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.25/0.51  thf('47', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (((u1_struct_0 @ sk_A) = (X0))
% 0.25/0.51          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51              != (g1_pre_topc @ X0 @ X1)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.25/0.51  thf('48', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))
% 0.25/0.51            != (X0))
% 0.25/0.51          | ~ (l1_pre_topc @ X0)
% 0.25/0.51          | ~ (v1_pre_topc @ X0)
% 0.25/0.51          | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['44', '47'])).
% 0.25/0.51  thf('49', plain,
% 0.25/0.51      ((((u1_struct_0 @ sk_A)
% 0.25/0.51          = (u1_struct_0 @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))
% 0.25/0.51        | ~ (v1_pre_topc @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))
% 0.25/0.51        | ~ (l1_pre_topc @ 
% 0.25/0.51             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B))))),
% 0.25/0.51      inference('simplify', [status(thm)], ['48'])).
% 0.25/0.51  thf('50', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('51', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('52', plain, ((v1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.25/0.51  thf('53', plain,
% 0.25/0.51      (((k6_tmap_1 @ sk_A @ sk_B)
% 0.25/0.51         = (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('clc', [status(thm)], ['20', '21'])).
% 0.25/0.51  thf('54', plain, ((l1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B))),
% 0.25/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.25/0.51  thf('55', plain,
% 0.25/0.51      (((u1_struct_0 @ sk_A) = (u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('demod', [status(thm)], ['49', '50', '51', '52', '53', '54'])).
% 0.25/0.51  thf('56', plain,
% 0.25/0.51      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) != (u1_struct_0 @ sk_A)))
% 0.25/0.51         <= (~
% 0.25/0.51             (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.25/0.51      inference('split', [status(esa)], ['0'])).
% 0.25/0.51  thf('57', plain,
% 0.25/0.51      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)))
% 0.25/0.51         <= (~
% 0.25/0.51             (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))),
% 0.25/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.25/0.51  thf('58', plain,
% 0.25/0.51      ((((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('simplify', [status(thm)], ['57'])).
% 0.25/0.51  thf('59', plain,
% 0.25/0.51      (~
% 0.25/0.51       (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B))) | 
% 0.25/0.51       ~ (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 0.25/0.51      inference('split', [status(esa)], ['0'])).
% 0.25/0.51  thf('60', plain,
% 0.25/0.51      (~
% 0.25/0.51       (((u1_pre_topc @ (k6_tmap_1 @ sk_A @ sk_B)) = (k5_tmap_1 @ sk_A @ sk_B)))),
% 0.25/0.51      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.25/0.51  thf('61', plain, ($false),
% 0.25/0.51      inference('simpl_trail', [status(thm)], ['43', '60'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
