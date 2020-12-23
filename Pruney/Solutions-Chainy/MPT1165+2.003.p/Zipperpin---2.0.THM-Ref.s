%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ghKFVCeTMJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 (1499 expanded)
%              Number of leaves         :   24 ( 386 expanded)
%              Depth                    :   24
%              Number of atoms          : 1407 (27549 expanded)
%              Number of equality atoms :   49 (1993 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
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

thf('43',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r3_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( r3_orders_2 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r3_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(t30_orders_2,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ~ ( ( r1_orders_2 @ A @ B @ C )
                  & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_orders_2 @ X14 @ X15 @ X13 )
      | ~ ( r1_orders_2 @ X14 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t30_orders_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('71',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
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
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0
        = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','83'])).

thf('85',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('86',plain,
    ( ( sk_B
      = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( sk_B
    = ( k3_orders_2 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
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

thf('90',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k3_orders_2 @ X17 @ X18 @ X19 ) )
      | ( r2_orders_2 @ X17 @ X16 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('91',plain,(
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
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_orders_2 @ sk_A @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['72','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
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

thf('104',plain,(
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
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','32'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_orders_2 @ sk_B @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,(
    m1_orders_2 @ sk_B @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf('114',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    r2_orders_2 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['117','118'])).

thf('120',plain,(
    $false ),
    inference(demod,[status(thm)],['71','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ghKFVCeTMJ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 54 iterations in 0.032s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(t68_orders_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.21/0.49             ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.21/0.49                  ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49              ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( m1_orders_2 @ B @ A @ B ) ) ) & 
% 0.21/0.49                ( ~( ( ~( m1_orders_2 @ B @ A @ B ) ) & 
% 0.21/0.49                     ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t68_orders_2])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d15_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49               ( ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.21/0.49                     ( ?[D:$i]:
% 0.21/0.49                       ( ( ( C ) = ( k3_orders_2 @ A @ B @ D ) ) & 
% 0.21/0.49                         ( r2_hidden @ D @ B ) & 
% 0.21/0.49                         ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) & 
% 0.21/0.49                 ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.49                   ( ( m1_orders_2 @ C @ A @ B ) <=>
% 0.21/0.49                     ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ (u1_struct_0 @ X1))
% 0.21/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (l1_orders_2 @ X1)
% 0.21/0.49          | ~ (v5_orders_2 @ X1)
% 0.21/0.49          | ~ (v4_orders_2 @ X1)
% 0.21/0.49          | ~ (v3_orders_2 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((((sk_B) != (k1_xboole_0)) | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (~ (((sk_B) = (k1_xboole_0))) | ~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.49         <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ((X0) != (k1_xboole_0))
% 0.21/0.49          | (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.49          | ((X2) != (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (l1_orders_2 @ X1)
% 0.21/0.49          | ~ (v5_orders_2 @ X1)
% 0.21/0.49          | ~ (v4_orders_2 @ X1)
% 0.21/0.49          | ~ (v3_orders_2 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X1)
% 0.21/0.49          | ~ (v3_orders_2 @ X1)
% 0.21/0.49          | ~ (v4_orders_2 @ X1)
% 0.21/0.49          | ~ (v5_orders_2 @ X1)
% 0.21/0.49          | ~ (l1_orders_2 @ X1)
% 0.21/0.49          | (m1_orders_2 @ k1_xboole_0 @ X1 @ k1_xboole_0)
% 0.21/0.49          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.49         | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49         | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49         | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49         | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '17'])).
% 0.21/0.49  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.49         | (v2_struct_0 @ sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.49  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.21/0.49         <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.21/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['9'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ sk_B))
% 0.21/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.21/0.49             (((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((~ (m1_orders_2 @ k1_xboole_0 @ sk_A @ k1_xboole_0))
% 0.21/0.49         <= (~ ((m1_orders_2 @ sk_B @ sk_A @ sk_B)) & 
% 0.21/0.49             (((sk_B) = (k1_xboole_0))))),
% 0.21/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.49  thf('32', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['11', '31'])).
% 0.21/0.49  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['8', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B))
% 0.21/0.49         <= (((m1_orders_2 @ sk_B @ sk_A @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((m1_orders_2 @ sk_B @ sk_A @ sk_B)) | (((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('split', [status(esa)], ['12'])).
% 0.21/0.49  thf('38', plain, (((m1_orders_2 @ sk_B @ sk_A @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['11', '31', '37'])).
% 0.21/0.49  thf('39', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '39'])).
% 0.21/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(reflexivity_r3_orders_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( r3_orders_2 @ A @ B @ B ) ))).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((r3_orders_2 @ X10 @ X11 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.21/0.49          | ~ (l1_orders_2 @ X10)
% 0.21/0.49          | ~ (v3_orders_2 @ X10)
% 0.21/0.49          | (v2_struct_0 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | (r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49             (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | (r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49             (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.49  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49        (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (l1_orders_2 @ X8)
% 0.21/0.49          | ~ (v3_orders_2 @ X8)
% 0.21/0.49          | (v2_struct_0 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.49          | (r1_orders_2 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (r3_orders_2 @ X8 @ X7 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r3_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.49  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49        (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf(t30_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ~( ( r1_orders_2 @ A @ B @ C ) & ( r2_orders_2 @ A @ C @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (r2_orders_2 @ X14 @ X15 @ X13)
% 0.21/0.49          | ~ (r1_orders_2 @ X14 @ X13 @ X15)
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (l1_orders_2 @ X14)
% 0.21/0.49          | ~ (v5_orders_2 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t30_orders_2])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.49  thf('66', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (r1_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ X0)
% 0.21/0.49          | ~ (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((~ (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (~ (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49          (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k3_orders_2 @ X1 @ X0 @ (sk_D @ X2 @ X0 @ X1)))
% 0.21/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (l1_orders_2 @ X1)
% 0.21/0.49          | ~ (v5_orders_2 @ X1)
% 0.21/0.49          | ~ (v4_orders_2 @ X1)
% 0.21/0.49          | ~ (v3_orders_2 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('78', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('79', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('80', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A)))
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.21/0.49  thf('82', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | ((X0) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.21/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '83'])).
% 0.21/0.49  thf('85', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      ((((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.49  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('88', plain,
% 0.21/0.49      (((sk_B) = (k3_orders_2 @ sk_A @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('clc', [status(thm)], ['86', '87'])).
% 0.21/0.49  thf('89', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t57_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.21/0.49                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.49          | ~ (r2_hidden @ X16 @ (k3_orders_2 @ X17 @ X18 @ X19))
% 0.21/0.49          | (r2_orders_2 @ X17 @ X16 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.21/0.49          | ~ (l1_orders_2 @ X17)
% 0.21/0.49          | ~ (v5_orders_2 @ X17)
% 0.21/0.49          | ~ (v4_orders_2 @ X17)
% 0.21/0.49          | ~ (v3_orders_2 @ X17)
% 0.21/0.49          | (v2_struct_0 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.49  thf('92', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('93', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('94', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('96', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ X1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X1 @ (k3_orders_2 @ sk_A @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.21/0.49  thf('97', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.49          | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['88', '96'])).
% 0.21/0.49  thf('98', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('99', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | (r2_orders_2 @ sk_A @ X0 @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.49  thf('100', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A))
% 0.21/0.49        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['72', '99'])).
% 0.21/0.49  thf('101', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('102', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('103', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | (r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X0)
% 0.21/0.49          | ~ (m1_orders_2 @ X2 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (l1_orders_2 @ X1)
% 0.21/0.49          | ~ (v5_orders_2 @ X1)
% 0.21/0.49          | ~ (v4_orders_2 @ X1)
% 0.21/0.49          | ~ (v3_orders_2 @ X1)
% 0.21/0.49          | (v2_struct_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d15_orders_2])).
% 0.21/0.49  thf('104', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.49  thf('105', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('106', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('107', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('108', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('109', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49          | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.21/0.49  thf('110', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['10', '32'])).
% 0.21/0.49  thf('111', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.49          | (r2_hidden @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['109', '110'])).
% 0.21/0.49  thf('112', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | ~ (m1_orders_2 @ sk_B @ sk_A @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['101', '111'])).
% 0.21/0.49  thf('113', plain, ((m1_orders_2 @ sk_B @ sk_A @ sk_B)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['36', '38'])).
% 0.21/0.49  thf('114', plain,
% 0.21/0.49      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['112', '113'])).
% 0.21/0.49  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('116', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['114', '115'])).
% 0.21/0.49  thf('117', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | (r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49           (sk_D @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['100', '116'])).
% 0.21/0.49  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('119', plain,
% 0.21/0.49      ((r2_orders_2 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A) @ 
% 0.21/0.49        (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['117', '118'])).
% 0.21/0.49  thf('120', plain, ($false), inference('demod', [status(thm)], ['71', '119'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
