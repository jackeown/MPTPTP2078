%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.svD9dPC1qH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 463 expanded)
%              Number of leaves         :   18 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  919 (8327 expanded)
%              Number of equality atoms :   49 ( 610 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t68_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ~ ( ( B != k1_xboole_0 )
                & ( m1_orders_2 @ B @ A @ B ) )
            & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ B ) )
              & ~ ( ~ ( m1_orders_2 @ B @ A @ B )
                  & ( B = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_orders_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( B != k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ? [D: $i] :
                        ( ( C
                          = ( k3_orders_2 @ A @ B @ D ) )
                        & ( r2_hidden @ D @ B )
                        & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) )
                & ( ( B = k1_xboole_0 )
                 => ( ( m1_orders_2 @ C @ A @ B )
                  <=> ( C = k1_xboole_0 ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X2
        = ( k3_orders_2 @ X1 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('12',plain,
    ( ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 != k1_xboole_0 )
      | ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ( X2 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ( m1_orders_2 @ k1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,
    ( ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
   <= ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('28',plain,
    ( ~ ( m1_orders_2 @ k1_xboole_0 @ sk_A @ sk_B )
   <= ( ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('30',plain,
    ( ~ ( m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0 )
   <= ( ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['11','31'])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','34'])).

thf('36',plain,
    ( ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
   <= ( m1_orders_2 @ sk_B @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('38',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['11','31','37'])).

thf('39',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('40',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_B
    = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t62_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( r2_hidden @ B @ ( k3_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ ( k3_orders_2 @ X5 @ X6 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v5_orders_2 @ X5 )
      | ~ ( v4_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t62_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X0 )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','64'])).

thf('66',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_orders_2 @ X2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['53','69','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.svD9dPC1qH
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:11 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 36 iterations in 0.021s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.23/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.23/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.49  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.23/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.49  thf(t68_orders_2, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.23/0.49             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.23/0.49                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.49          ( ![B:$i]:
% 0.23/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49              ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.23/0.49                ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.23/0.49                     ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t68_orders_2])).
% 0.23/0.49  thf('0', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(d15_orders_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49           ( ![C:$i]:
% 0.23/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.49                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.23/0.49                     ( ?[D:$i]:
% 0.23/0.49                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.23/0.49                         ( r2_hidden @ D @ B ) & 
% 0.23/0.49                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.23/0.49                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.49                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.23/0.49                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ((X0) = (k1_xboole_0))
% 0.23/0.49          | ((X2) = (k3_orders_2 @ X1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 0.23/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ~ (l1_orders_2 @ X1)
% 0.23/0.49          | ~ (v5_orders_2 @ X1)
% 0.23/0.49          | ~ (v4_orders_2 @ X1)
% 0.23/0.49          | ~ (v3_orders_2 @ X1)
% 0.23/0.49          | (v2_struct_0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.23/0.49  thf('3', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.49  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('8', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      ((((sk_B) != (k1_xboole_0)) | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('split', [status(esa)], ['9'])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (~ (((sk_B) = (k1_xboole_0))) | ~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.23/0.49      inference('split', [status(esa)], ['9'])).
% 0.23/0.49  thf('12', plain,
% 0.23/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('split', [status(esa)], ['12'])).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('15', plain,
% 0.23/0.49      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.23/0.49         <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ((X0) != (k1_xboole_0))
% 0.23/0.49          | (m1_orders_2 @ X2 @ X1 @ X0)
% 0.23/0.49          | ((X2) != (k1_xboole_0))
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ~ (l1_orders_2 @ X1)
% 0.23/0.49          | ~ (v5_orders_2 @ X1)
% 0.23/0.49          | ~ (v4_orders_2 @ X1)
% 0.23/0.49          | ~ (v3_orders_2 @ X1)
% 0.23/0.49          | (v2_struct_0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      (![X1 : $i]:
% 0.23/0.49         ((v2_struct_0 @ X1)
% 0.23/0.49          | ~ (v3_orders_2 @ X1)
% 0.23/0.49          | ~ (v4_orders_2 @ X1)
% 0.23/0.49          | ~ (v5_orders_2 @ X1)
% 0.23/0.49          | ~ (l1_orders_2 @ X1)
% 0.23/0.49          | (m1_orders_2 @ k1_xboole_0 @ X1 @ k1_xboole_0)
% 0.23/0.49          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.23/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.49  thf('18', plain,
% 0.23/0.49      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.23/0.49         | ~ (l1_orders_2 @ sk_A)
% 0.23/0.49         | ~ (v5_orders_2 @ sk_A)
% 0.23/0.49         | ~ (v4_orders_2 @ sk_A)
% 0.23/0.49         | ~ (v3_orders_2 @ sk_A)
% 0.23/0.49         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['15', '17'])).
% 0.23/0.49  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('23', plain,
% 0.23/0.49      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.23/0.49         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.23/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('25', plain,
% 0.23/0.49      (((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.23/0.49         <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('26', plain,
% 0.23/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('split', [status(esa)], ['12'])).
% 0.23/0.49  thf('27', plain,
% 0.23/0.49      ((~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.23/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.23/0.49      inference('split', [status(esa)], ['9'])).
% 0.23/0.49  thf('28', plain,
% 0.23/0.49      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.23/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.23/0.49             (((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.49  thf('29', plain,
% 0.23/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('split', [status(esa)], ['12'])).
% 0.23/0.49  thf('30', plain,
% 0.23/0.49      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.23/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.23/0.49             (((sk_B) = (k1_xboole_0))))),
% 0.23/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.49  thf('31', plain,
% 0.23/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['25', '30'])).
% 0.23/0.49  thf('32', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['11', '31'])).
% 0.23/0.49  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.23/0.49  thf('34', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['8', '33'])).
% 0.23/0.49  thf('35', plain,
% 0.23/0.49      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.23/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['0', '34'])).
% 0.23/0.49  thf('36', plain,
% 0.23/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.23/0.49         <= (((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.23/0.49      inference('split', [status(esa)], ['12'])).
% 0.23/0.49  thf('37', plain,
% 0.23/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | (((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('split', [status(esa)], ['12'])).
% 0.23/0.49  thf('38', plain, (((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.23/0.49      inference('sat_resolution*', [status(thm)], ['11', '31', '37'])).
% 0.23/0.49  thf('39', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.23/0.49  thf('40', plain,
% 0.23/0.49      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['35', '39'])).
% 0.23/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('42', plain,
% 0.23/0.49      (((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.23/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.23/0.49  thf('43', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t62_orders_2, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.49       ( ![B:$i]:
% 0.23/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.49           ( ![C:$i]:
% 0.23/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.49               ( ~( r2_hidden @ B @ ( k3_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf('44', plain,
% 0.23/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X5))
% 0.23/0.49          | ~ (r2_hidden @ X4 @ (k3_orders_2 @ X5 @ X6 @ X4))
% 0.23/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.23/0.49          | ~ (l1_orders_2 @ X5)
% 0.23/0.49          | ~ (v5_orders_2 @ X5)
% 0.23/0.49          | ~ (v4_orders_2 @ X5)
% 0.23/0.49          | ~ (v3_orders_2 @ X5)
% 0.23/0.49          | (v2_struct_0 @ X5))),
% 0.23/0.49      inference('cnf', [status(esa)], [t62_orders_2])).
% 0.23/0.49  thf('45', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.49          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.23/0.49  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('50', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.23/0.49  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('52', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.23/0.49          | ~ (r2_hidden @ X0 @ (k3_orders_2 @ sk_A @ sk_B @ X0)))),
% 0.23/0.49      inference('clc', [status(thm)], ['50', '51'])).
% 0.23/0.49  thf('53', plain,
% 0.23/0.49      ((~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.23/0.49        | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['42', '52'])).
% 0.23/0.49  thf('54', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('55', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('56', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ((X0) = (k1_xboole_0))
% 0.23/0.49          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X0)
% 0.23/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ~ (l1_orders_2 @ X1)
% 0.23/0.49          | ~ (v5_orders_2 @ X1)
% 0.23/0.49          | ~ (v4_orders_2 @ X1)
% 0.23/0.49          | ~ (v3_orders_2 @ X1)
% 0.23/0.49          | (v2_struct_0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.23/0.49  thf('57', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.49  thf('58', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('59', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('62', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.23/0.49  thf('63', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.23/0.49  thf('64', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 0.23/0.49  thf('65', plain,
% 0.23/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.23/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['54', '64'])).
% 0.23/0.49  thf('66', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.23/0.49  thf('67', plain,
% 0.23/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.23/0.49  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('69', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.23/0.49      inference('clc', [status(thm)], ['67', '68'])).
% 0.23/0.49  thf('70', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('71', plain,
% 0.23/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('72', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ((X0) = (k1_xboole_0))
% 0.23/0.49          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 0.23/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.23/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.23/0.49          | ~ (l1_orders_2 @ X1)
% 0.23/0.49          | ~ (v5_orders_2 @ X1)
% 0.23/0.49          | ~ (v4_orders_2 @ X1)
% 0.23/0.49          | ~ (v3_orders_2 @ X1)
% 0.23/0.49          | (v2_struct_0 @ X1))),
% 0.23/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.23/0.49  thf('73', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.23/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.23/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.23/0.49  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('78', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.23/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.49      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 0.23/0.49  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.23/0.49  thf('80', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((v2_struct_0 @ sk_A)
% 0.23/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.23/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.23/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.23/0.49  thf('81', plain,
% 0.23/0.49      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.23/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('sup-', [status(thm)], ['70', '80'])).
% 0.23/0.49  thf('82', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.23/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.23/0.49  thf('83', plain,
% 0.23/0.49      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.23/0.49        | (v2_struct_0 @ sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['81', '82'])).
% 0.23/0.49  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('85', plain,
% 0.23/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.23/0.49      inference('clc', [status(thm)], ['83', '84'])).
% 0.23/0.49  thf('86', plain, ($false),
% 0.23/0.49      inference('demod', [status(thm)], ['53', '69', '85'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
