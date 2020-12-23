%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oP1Bd88Opb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:05 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 758 expanded)
%              Number of leaves         :   21 ( 201 expanded)
%              Depth                    :   20
%              Number of atoms          : 1096 (13782 expanded)
%              Number of equality atoms :   51 (1002 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X3 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 != k1_xboole_0 )
      | ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ( X5 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ( m1_orders_2 @ k1_xboole_0 @ X4 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
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
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( X5
        = ( k3_orders_2 @ X4 @ X3 @ ( sk_D @ X5 @ X3 @ X4 ) ) )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('52',plain,(
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
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','59'])).

thf('61',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('62',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_B
    = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r2_hidden @ X7 @ ( k3_orders_2 @ X8 @ X9 @ X10 ) )
      | ( r2_orders_2 @ X8 @ X7 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X5 @ X3 @ X4 ) @ X3 )
      | ~ ( m1_orders_2 @ X5 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d15_orders_2])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('90',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['47','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oP1Bd88Opb
% 0.06/0.26  % Computer   : n004.cluster.edu
% 0.06/0.26  % Model      : x86_64 x86_64
% 0.06/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.26  % Memory     : 8042.1875MB
% 0.06/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.26  % CPULimit   : 60
% 0.06/0.26  % DateTime   : Tue Dec  1 13:20:08 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  % Running portfolio for 600 s
% 0.06/0.26  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.06/0.26  % Number of cores: 8
% 0.06/0.27  % Python version: Python 3.6.8
% 0.06/0.27  % Running in FO mode
% 0.11/0.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.11/0.40  % Solved by: fo/fo7.sh
% 0.11/0.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.11/0.40  % done 47 iterations in 0.029s
% 0.11/0.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.11/0.40  % SZS output start Refutation
% 0.11/0.40  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.11/0.40  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.11/0.40  thf(sk_B_type, type, sk_B: $i).
% 0.11/0.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.11/0.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.11/0.40  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.11/0.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.11/0.40  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.11/0.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.11/0.40  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.11/0.40  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.11/0.40  thf(sk_A_type, type, sk_A: $i).
% 0.11/0.40  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.11/0.40  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.11/0.40  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.11/0.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.11/0.40  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.11/0.40  thf(t68_orders_2, conjecture,
% 0.11/0.40    (![A:$i]:
% 0.11/0.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.11/0.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.11/0.40       ( ![B:$i]:
% 0.11/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.11/0.40           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.11/0.40             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.11/0.40                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.11/0.40  thf(zf_stmt_0, negated_conjecture,
% 0.11/0.40    (~( ![A:$i]:
% 0.11/0.40        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.11/0.40            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.11/0.40          ( ![B:$i]:
% 0.11/0.40            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.11/0.40              ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.11/0.40                ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.11/0.40                     ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) )),
% 0.11/0.40    inference('cnf.neg', [status(esa)], [t68_orders_2])).
% 0.11/0.40  thf('0', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('1', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf(d15_orders_2, axiom,
% 0.11/0.40    (![A:$i]:
% 0.11/0.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.11/0.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.11/0.40       ( ![B:$i]:
% 0.11/0.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.11/0.40           ( ![C:$i]:
% 0.11/0.40             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.11/0.40               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.11/0.40                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.11/0.40                     ( ?[D:$i]:
% 0.11/0.40                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.11/0.40                         ( r2_hidden @ D @ B ) & 
% 0.11/0.40                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.11/0.40                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.11/0.40                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.11/0.40                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.11/0.40  thf('2', plain,
% 0.11/0.40      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ((X3) = (k1_xboole_0))
% 0.11/0.40          | (m1_subset_1 @ (sk_D @ X5 @ X3 @ X4) @ (u1_struct_0 @ X4))
% 0.11/0.40          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.11/0.40          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ~ (l1_orders_2 @ X4)
% 0.11/0.40          | ~ (v5_orders_2 @ X4)
% 0.11/0.40          | ~ (v4_orders_2 @ X4)
% 0.11/0.40          | ~ (v3_orders_2 @ X4)
% 0.11/0.40          | (v2_struct_0 @ X4))),
% 0.11/0.40      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.11/0.40  thf('3', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (v3_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v4_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v5_orders_2 @ sk_A)
% 0.11/0.40          | ~ (l1_orders_2 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('sup-', [status(thm)], ['1', '2'])).
% 0.11/0.40  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('8', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.11/0.40  thf('9', plain,
% 0.11/0.40      ((((sk_B) != (k1_xboole_0)) | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('10', plain,
% 0.11/0.40      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('split', [status(esa)], ['9'])).
% 0.11/0.40  thf('11', plain,
% 0.11/0.40      (~ (((sk_B) = (k1_xboole_0))) | ~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.11/0.40      inference('split', [status(esa)], ['9'])).
% 0.11/0.40  thf('12', plain,
% 0.11/0.40      (((m1_orders_2 @ sk_B @ sk_A @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('13', plain,
% 0.11/0.40      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('split', [status(esa)], ['12'])).
% 0.11/0.40  thf('14', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('15', plain,
% 0.11/0.40      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.11/0.40         <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('sup+', [status(thm)], ['13', '14'])).
% 0.11/0.40  thf('16', plain,
% 0.11/0.40      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ((X3) != (k1_xboole_0))
% 0.11/0.40          | (m1_orders_2 @ X5 @ X4 @ X3)
% 0.11/0.40          | ((X5) != (k1_xboole_0))
% 0.11/0.40          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ~ (l1_orders_2 @ X4)
% 0.11/0.40          | ~ (v5_orders_2 @ X4)
% 0.11/0.40          | ~ (v4_orders_2 @ X4)
% 0.11/0.40          | ~ (v3_orders_2 @ X4)
% 0.11/0.40          | (v2_struct_0 @ X4))),
% 0.11/0.40      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.11/0.40  thf('17', plain,
% 0.11/0.40      (![X4 : $i]:
% 0.11/0.40         ((v2_struct_0 @ X4)
% 0.11/0.40          | ~ (v3_orders_2 @ X4)
% 0.11/0.40          | ~ (v4_orders_2 @ X4)
% 0.11/0.40          | ~ (v5_orders_2 @ X4)
% 0.11/0.40          | ~ (l1_orders_2 @ X4)
% 0.11/0.40          | (m1_orders_2 @ k1_xboole_0 @ X4 @ k1_xboole_0)
% 0.11/0.40          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.11/0.40      inference('simplify', [status(thm)], ['16'])).
% 0.11/0.40  thf('18', plain,
% 0.11/0.40      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.11/0.40         | ~ (l1_orders_2 @ sk_A)
% 0.11/0.40         | ~ (v5_orders_2 @ sk_A)
% 0.11/0.40         | ~ (v4_orders_2 @ sk_A)
% 0.11/0.40         | ~ (v3_orders_2 @ sk_A)
% 0.11/0.40         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('sup-', [status(thm)], ['15', '17'])).
% 0.11/0.40  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('23', plain,
% 0.11/0.40      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.11/0.40         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.11/0.40  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('25', plain,
% 0.11/0.40      (((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.11/0.40         <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('clc', [status(thm)], ['23', '24'])).
% 0.11/0.40  thf('26', plain,
% 0.11/0.40      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('split', [status(esa)], ['12'])).
% 0.11/0.40  thf('27', plain,
% 0.11/0.40      ((~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.11/0.40         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.11/0.40      inference('split', [status(esa)], ['9'])).
% 0.11/0.40  thf('28', plain,
% 0.11/0.40      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.11/0.40         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.11/0.40             (((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('sup-', [status(thm)], ['26', '27'])).
% 0.11/0.40  thf('29', plain,
% 0.11/0.40      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('split', [status(esa)], ['12'])).
% 0.11/0.40  thf('30', plain,
% 0.11/0.40      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.11/0.40         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.11/0.40             (((sk_B) = (k1_xboole_0))))),
% 0.11/0.40      inference('demod', [status(thm)], ['28', '29'])).
% 0.11/0.40  thf('31', plain,
% 0.11/0.40      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('sup-', [status(thm)], ['25', '30'])).
% 0.11/0.40  thf('32', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('sat_resolution*', [status(thm)], ['11', '31'])).
% 0.11/0.40  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.11/0.40  thf('34', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('simplify_reflect-', [status(thm)], ['8', '33'])).
% 0.11/0.40  thf('35', plain,
% 0.11/0.40      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.11/0.40        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.11/0.40        | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('sup-', [status(thm)], ['0', '34'])).
% 0.11/0.40  thf('36', plain,
% 0.11/0.40      (((m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.11/0.40         <= (((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.11/0.40      inference('split', [status(esa)], ['12'])).
% 0.11/0.40  thf('37', plain,
% 0.11/0.40      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | (((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('split', [status(esa)], ['12'])).
% 0.11/0.40  thf('38', plain, (((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.11/0.40      inference('sat_resolution*', [status(thm)], ['11', '31', '37'])).
% 0.11/0.40  thf('39', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.11/0.40  thf('40', plain,
% 0.11/0.40      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.11/0.40        | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('demod', [status(thm)], ['35', '39'])).
% 0.11/0.40  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('42', plain,
% 0.11/0.40      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.11/0.40      inference('clc', [status(thm)], ['40', '41'])).
% 0.11/0.40  thf(d10_orders_2, axiom,
% 0.11/0.40    (![A:$i]:
% 0.11/0.40     ( ( l1_orders_2 @ A ) =>
% 0.11/0.40       ( ![B:$i]:
% 0.11/0.40         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.11/0.40           ( ![C:$i]:
% 0.11/0.40             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.11/0.40               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.11/0.40                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.11/0.40  thf('43', plain,
% 0.11/0.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.11/0.40          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.11/0.40          | ((X0) != (X2))
% 0.11/0.40          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.11/0.40          | ~ (l1_orders_2 @ X1))),
% 0.11/0.40      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.11/0.40  thf('44', plain,
% 0.11/0.40      (![X1 : $i, X2 : $i]:
% 0.11/0.40         (~ (l1_orders_2 @ X1)
% 0.11/0.40          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.11/0.40          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.11/0.40      inference('simplify', [status(thm)], ['43'])).
% 0.11/0.40  thf('45', plain,
% 0.11/0.40      ((~ (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.11/0.40           (sk_D @ sk_B @ sk_B @ sk_A))
% 0.11/0.40        | ~ (l1_orders_2 @ sk_A))),
% 0.11/0.40      inference('sup-', [status(thm)], ['42', '44'])).
% 0.11/0.40  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('47', plain,
% 0.11/0.40      (~ (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.11/0.40          (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.11/0.40      inference('demod', [status(thm)], ['45', '46'])).
% 0.11/0.40  thf('48', plain,
% 0.11/0.40      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.11/0.40      inference('clc', [status(thm)], ['40', '41'])).
% 0.11/0.40  thf('49', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('50', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('51', plain,
% 0.11/0.40      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ((X3) = (k1_xboole_0))
% 0.11/0.40          | ((X5) = (k3_orders_2 @ X4 @ X3 @ (sk_D @ X5 @ X3 @ X4)))
% 0.11/0.40          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.11/0.40          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ~ (l1_orders_2 @ X4)
% 0.11/0.40          | ~ (v5_orders_2 @ X4)
% 0.11/0.40          | ~ (v4_orders_2 @ X4)
% 0.11/0.40          | ~ (v3_orders_2 @ X4)
% 0.11/0.40          | (v2_struct_0 @ X4))),
% 0.11/0.40      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.11/0.40  thf('52', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (v3_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v4_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v5_orders_2 @ sk_A)
% 0.11/0.40          | ~ (l1_orders_2 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('sup-', [status(thm)], ['50', '51'])).
% 0.11/0.40  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('57', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.11/0.40  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.11/0.40  thf('59', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))))),
% 0.11/0.40      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.11/0.40  thf('60', plain,
% 0.11/0.40      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.11/0.40        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.11/0.40        | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('sup-', [status(thm)], ['49', '59'])).
% 0.11/0.40  thf('61', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.11/0.40  thf('62', plain,
% 0.11/0.40      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.11/0.40        | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('demod', [status(thm)], ['60', '61'])).
% 0.11/0.40  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('64', plain,
% 0.11/0.40      (((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.11/0.40      inference('clc', [status(thm)], ['62', '63'])).
% 0.11/0.40  thf('65', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf(t57_orders_2, axiom,
% 0.11/0.40    (![A:$i]:
% 0.11/0.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.11/0.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.11/0.40       ( ![B:$i]:
% 0.11/0.40         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.11/0.40           ( ![C:$i]:
% 0.11/0.40             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.11/0.40               ( ![D:$i]:
% 0.11/0.40                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.11/0.40                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.11/0.40                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.11/0.40  thf('66', plain,
% 0.11/0.40      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.11/0.40          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.11/0.40          | ~ (r2_hidden @ X7 @ (k3_orders_2 @ X8 @ X9 @ X10))
% 0.11/0.40          | (r2_orders_2 @ X8 @ X7 @ X10)
% 0.11/0.40          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.11/0.40          | ~ (l1_orders_2 @ X8)
% 0.11/0.40          | ~ (v5_orders_2 @ X8)
% 0.11/0.40          | ~ (v4_orders_2 @ X8)
% 0.11/0.40          | ~ (v3_orders_2 @ X8)
% 0.11/0.40          | (v2_struct_0 @ X8))),
% 0.11/0.40      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.11/0.40  thf('67', plain,
% 0.11/0.40      (![X0 : $i, X1 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (v3_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v4_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v5_orders_2 @ sk_A)
% 0.11/0.40          | ~ (l1_orders_2 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.11/0.40          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.11/0.40          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('sup-', [status(thm)], ['65', '66'])).
% 0.11/0.40  thf('68', plain, ((v3_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('69', plain, ((v4_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('70', plain, ((v5_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('71', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('72', plain,
% 0.11/0.40      (![X0 : $i, X1 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.11/0.40          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.11/0.40          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.11/0.40  thf('73', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         (~ (r2_hidden @ X0 @ sk_B)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.11/0.40          | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('sup-', [status(thm)], ['64', '72'])).
% 0.11/0.40  thf('74', plain,
% 0.11/0.40      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.11/0.40      inference('clc', [status(thm)], ['40', '41'])).
% 0.11/0.40  thf('75', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         (~ (r2_hidden @ X0 @ sk_B)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.11/0.40          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.11/0.40          | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('demod', [status(thm)], ['73', '74'])).
% 0.11/0.40  thf('76', plain,
% 0.11/0.40      (((v2_struct_0 @ sk_A)
% 0.11/0.40        | (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.11/0.40           (sk_D @ sk_B @ sk_B @ sk_A))
% 0.11/0.40        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B))),
% 0.11/0.40      inference('sup-', [status(thm)], ['48', '75'])).
% 0.11/0.40  thf('77', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('78', plain,
% 0.11/0.40      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('79', plain,
% 0.11/0.40      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.11/0.40         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ((X3) = (k1_xboole_0))
% 0.11/0.40          | (r2_hidden @ (sk_D @ X5 @ X3 @ X4) @ X3)
% 0.11/0.40          | ~ (m1_orders_2 @ X5 @ X4 @ X3)
% 0.11/0.40          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.11/0.40          | ~ (l1_orders_2 @ X4)
% 0.11/0.40          | ~ (v5_orders_2 @ X4)
% 0.11/0.40          | ~ (v4_orders_2 @ X4)
% 0.11/0.40          | ~ (v3_orders_2 @ X4)
% 0.11/0.40          | (v2_struct_0 @ X4))),
% 0.11/0.40      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.11/0.40  thf('80', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (v3_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v4_orders_2 @ sk_A)
% 0.11/0.40          | ~ (v5_orders_2 @ sk_A)
% 0.11/0.40          | ~ (l1_orders_2 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('sup-', [status(thm)], ['78', '79'])).
% 0.11/0.40  thf('81', plain, ((v3_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('82', plain, ((v4_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('83', plain, ((v5_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('85', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.11/0.40          | ((sk_B) = (k1_xboole_0)))),
% 0.11/0.40      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.11/0.40  thf('86', plain, (((sk_B) != (k1_xboole_0))),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.11/0.40  thf('87', plain,
% 0.11/0.40      (![X0 : $i]:
% 0.11/0.40         ((v2_struct_0 @ sk_A)
% 0.11/0.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.11/0.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.11/0.40          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.11/0.40      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.11/0.40  thf('88', plain,
% 0.11/0.40      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.11/0.40        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.11/0.40        | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('sup-', [status(thm)], ['77', '87'])).
% 0.11/0.40  thf('89', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.11/0.40      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.11/0.40  thf('90', plain,
% 0.11/0.40      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.11/0.40      inference('demod', [status(thm)], ['88', '89'])).
% 0.11/0.40  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('92', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.11/0.40      inference('clc', [status(thm)], ['90', '91'])).
% 0.11/0.40  thf('93', plain,
% 0.11/0.40      (((v2_struct_0 @ sk_A)
% 0.11/0.40        | (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.11/0.40           (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.11/0.40      inference('demod', [status(thm)], ['76', '92'])).
% 0.11/0.40  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.11/0.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.11/0.40  thf('95', plain,
% 0.11/0.40      ((r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.11/0.40        (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.11/0.40      inference('clc', [status(thm)], ['93', '94'])).
% 0.11/0.40  thf('96', plain, ($false), inference('demod', [status(thm)], ['47', '95'])).
% 0.11/0.40  
% 0.11/0.40  % SZS output end Refutation
% 0.11/0.40  
% 0.11/0.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
