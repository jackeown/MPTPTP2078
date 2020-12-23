%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.laIudLoO2D

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:42 EST 2020

% Result     : Theorem 2.60s
% Output     : Refutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  173 (2892 expanded)
%              Number of leaves         :   37 ( 896 expanded)
%              Depth                    :   29
%              Number of atoms          : 1467 (27933 expanded)
%              Number of equality atoms :   76 (1900 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t46_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t46_orders_2])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( ( k1_struct_0 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('8',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    ! [X12: $i] :
      ( ( ( k1_struct_0 @ X12 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('11',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t45_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X25: $i] :
      ( ( ( k2_orders_2 @ X25 @ ( k1_struct_0 @ X25 ) )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t45_orders_2])).

thf('13',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','24'])).

thf('26',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('28',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(fraenkel_a_2_1_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ D @ E ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X20 @ X23 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('32',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(d13_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_orders_2 @ A @ B )
            = ( a_2_1_orders_2 @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_orders_2 @ X18 @ X17 )
        = ( a_2_1_orders_2 @ X18 @ X17 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('55',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('56',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('57',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( X23
        = ( sk_D @ X21 @ X20 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','71'])).

thf('73',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

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

thf('76',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_orders_2 @ X15 @ X14 @ X16 )
      | ( X14 != X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('77',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( r2_orders_2 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('85',plain,(
    ! [X20: $i,X21: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ( X23 != X24 )
      | ( r2_hidden @ ( sk_E @ X24 @ X21 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('86',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( r2_hidden @ ( sk_E @ X24 @ X21 @ X20 ) @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X20 ) )
      | ( r2_hidden @ X24 @ ( a_2_1_orders_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_struct_0 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('91',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('94',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','95','96','97','98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('104',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('105',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('107',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    r2_hidden @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('111',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('112',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ( r2_orders_2 @ X20 @ ( sk_D @ X21 @ X20 @ X23 ) @ X22 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('121',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['109','123'])).

thf('125',plain,
    ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['108','128'])).

thf('130',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['81','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.laIudLoO2D
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 2.60/2.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.60/2.81  % Solved by: fo/fo7.sh
% 2.60/2.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.60/2.81  % done 5264 iterations in 2.360s
% 2.60/2.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.60/2.81  % SZS output start Refutation
% 2.60/2.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.60/2.81  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.60/2.81  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.60/2.81  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 2.60/2.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.60/2.81  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.60/2.81  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.60/2.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.60/2.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.60/2.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.60/2.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.60/2.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.60/2.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.60/2.81  thf(sk_A_type, type, sk_A: $i).
% 2.60/2.81  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 2.60/2.81  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 2.60/2.81  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 2.60/2.81  thf(sk_B_type, type, sk_B: $i > $i).
% 2.60/2.81  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 2.60/2.81  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 2.60/2.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.60/2.81  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 2.60/2.81  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 2.60/2.81  thf(t7_xboole_0, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.60/2.81          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.60/2.81  thf('0', plain,
% 2.60/2.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.60/2.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.60/2.81  thf(dt_k2_subset_1, axiom,
% 2.60/2.81    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.60/2.81  thf('1', plain,
% 2.60/2.81      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 2.60/2.81      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.60/2.81  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.60/2.81  thf('2', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 2.60/2.81      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.60/2.81  thf('3', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 2.60/2.81      inference('demod', [status(thm)], ['1', '2'])).
% 2.60/2.81  thf(t46_orders_2, conjecture,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.60/2.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.60/2.81       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 2.60/2.81  thf(zf_stmt_0, negated_conjecture,
% 2.60/2.81    (~( ![A:$i]:
% 2.60/2.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.60/2.81            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.60/2.81          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 2.60/2.81    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 2.60/2.81  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf(dt_l1_orders_2, axiom,
% 2.60/2.81    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 2.60/2.81  thf('5', plain, (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_orders_2 @ X19))),
% 2.60/2.81      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 2.60/2.81  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.81      inference('sup-', [status(thm)], ['4', '5'])).
% 2.60/2.81  thf(d2_struct_0, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 2.60/2.81  thf('7', plain,
% 2.60/2.81      (![X12 : $i]:
% 2.60/2.81         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 2.60/2.81      inference('cnf', [status(esa)], [d2_struct_0])).
% 2.60/2.81  thf('8', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.81  thf(d3_struct_0, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.60/2.81  thf('9', plain,
% 2.60/2.81      (![X13 : $i]:
% 2.60/2.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 2.60/2.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.60/2.81  thf('10', plain,
% 2.60/2.81      (![X12 : $i]:
% 2.60/2.81         (((k1_struct_0 @ X12) = (k1_xboole_0)) | ~ (l1_struct_0 @ X12))),
% 2.60/2.81      inference('cnf', [status(esa)], [d2_struct_0])).
% 2.60/2.81  thf('11', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['6', '7'])).
% 2.60/2.81  thf(t45_orders_2, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.60/2.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.60/2.81       ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 2.60/2.81  thf('12', plain,
% 2.60/2.81      (![X25 : $i]:
% 2.60/2.81         (((k2_orders_2 @ X25 @ (k1_struct_0 @ X25)) = (u1_struct_0 @ X25))
% 2.60/2.81          | ~ (l1_orders_2 @ X25)
% 2.60/2.81          | ~ (v5_orders_2 @ X25)
% 2.60/2.81          | ~ (v4_orders_2 @ X25)
% 2.60/2.81          | ~ (v3_orders_2 @ X25)
% 2.60/2.81          | (v2_struct_0 @ X25))),
% 2.60/2.81      inference('cnf', [status(esa)], [t45_orders_2])).
% 2.60/2.81  thf('13', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 2.60/2.81        | (v2_struct_0 @ sk_A)
% 2.60/2.81        | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81        | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81        | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81        | ~ (l1_orders_2 @ sk_A))),
% 2.60/2.81      inference('sup+', [status(thm)], ['11', '12'])).
% 2.60/2.81  thf('14', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('18', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 2.60/2.81        | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 2.60/2.81  thf('19', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('20', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 2.60/2.81      inference('clc', [status(thm)], ['18', '19'])).
% 2.60/2.81  thf('21', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (u1_struct_0 @ sk_A))
% 2.60/2.81          | ~ (l1_struct_0 @ X0))),
% 2.60/2.81      inference('sup+', [status(thm)], ['10', '20'])).
% 2.60/2.81  thf('22', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (l1_struct_0 @ sk_A)
% 2.60/2.81          | ~ (l1_struct_0 @ X0))),
% 2.60/2.81      inference('sup+', [status(thm)], ['9', '21'])).
% 2.60/2.81  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.81      inference('sup-', [status(thm)], ['4', '5'])).
% 2.60/2.81  thf('24', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) = (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (l1_struct_0 @ X0))),
% 2.60/2.81      inference('demod', [status(thm)], ['22', '23'])).
% 2.60/2.81  thf('25', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))
% 2.60/2.81        | ~ (l1_struct_0 @ sk_A))),
% 2.60/2.81      inference('sup+', [status(thm)], ['8', '24'])).
% 2.60/2.81  thf('26', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 2.60/2.81      inference('clc', [status(thm)], ['18', '19'])).
% 2.60/2.81  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 2.60/2.81      inference('sup-', [status(thm)], ['4', '5'])).
% 2.60/2.81  thf('28', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf(fraenkel_a_2_1_orders_2, axiom,
% 2.60/2.81    (![A:$i,B:$i,C:$i]:
% 2.60/2.81     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 2.60/2.81         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 2.60/2.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 2.60/2.81       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 2.60/2.81         ( ?[D:$i]:
% 2.60/2.81           ( ( ![E:$i]:
% 2.60/2.81               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 2.60/2.81                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 2.60/2.81             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.60/2.81  thf('29', plain,
% 2.60/2.81      (![X20 : $i, X21 : $i, X23 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X20)
% 2.60/2.81          | ~ (v5_orders_2 @ X20)
% 2.60/2.81          | ~ (v4_orders_2 @ X20)
% 2.60/2.81          | ~ (v3_orders_2 @ X20)
% 2.60/2.81          | (v2_struct_0 @ X20)
% 2.60/2.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ X21 @ X20 @ X23) @ (u1_struct_0 @ X20))
% 2.60/2.81          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 2.60/2.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.60/2.81  thf('30', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (u1_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A))),
% 2.60/2.81      inference('sup-', [status(thm)], ['28', '29'])).
% 2.60/2.81  thf('31', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('36', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['30', '31', '32', '33', '34', '35'])).
% 2.60/2.81  thf('37', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         ((v2_struct_0 @ sk_A)
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 2.60/2.81             (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('sup-', [status(thm)], ['3', '36'])).
% 2.60/2.81  thf('38', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 2.60/2.81      inference('demod', [status(thm)], ['1', '2'])).
% 2.60/2.81  thf('39', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf(d13_orders_2, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.60/2.81         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.60/2.81       ( ![B:$i]:
% 2.60/2.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.60/2.81           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 2.60/2.81  thf('40', plain,
% 2.60/2.81      (![X17 : $i, X18 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.60/2.81          | ((k2_orders_2 @ X18 @ X17) = (a_2_1_orders_2 @ X18 @ X17))
% 2.60/2.81          | ~ (l1_orders_2 @ X18)
% 2.60/2.81          | ~ (v5_orders_2 @ X18)
% 2.60/2.81          | ~ (v4_orders_2 @ X18)
% 2.60/2.81          | ~ (v3_orders_2 @ X18)
% 2.60/2.81          | (v2_struct_0 @ X18))),
% 2.60/2.81      inference('cnf', [status(esa)], [d13_orders_2])).
% 2.60/2.81  thf('41', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A)
% 2.60/2.81          | ((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['39', '40'])).
% 2.60/2.81  thf('42', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('43', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('44', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('46', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0)))),
% 2.60/2.81      inference('demod', [status(thm)], ['41', '42', '43', '44', '45'])).
% 2.60/2.81  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('48', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('clc', [status(thm)], ['46', '47'])).
% 2.60/2.81  thf('49', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 2.60/2.81         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['38', '48'])).
% 2.60/2.81  thf('50', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         ((v2_struct_0 @ sk_A)
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 2.60/2.81             (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('demod', [status(thm)], ['37', '49'])).
% 2.60/2.81  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('52', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 2.60/2.81             (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('clc', [status(thm)], ['50', '51'])).
% 2.60/2.81  thf('53', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 2.60/2.81        | (m1_subset_1 @ 
% 2.60/2.81           (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 2.60/2.81            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 2.60/2.81           (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['0', '52'])).
% 2.60/2.81  thf('54', plain,
% 2.60/2.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.60/2.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.60/2.81  thf('55', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 2.60/2.81      inference('demod', [status(thm)], ['1', '2'])).
% 2.60/2.81  thf('56', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('57', plain,
% 2.60/2.81      (![X20 : $i, X21 : $i, X23 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X20)
% 2.60/2.81          | ~ (v5_orders_2 @ X20)
% 2.60/2.81          | ~ (v4_orders_2 @ X20)
% 2.60/2.81          | ~ (v3_orders_2 @ X20)
% 2.60/2.81          | (v2_struct_0 @ X20)
% 2.60/2.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.60/2.81          | ((X23) = (sk_D @ X21 @ X20 @ X23))
% 2.60/2.81          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 2.60/2.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.60/2.81  thf('58', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A))),
% 2.60/2.81      inference('sup-', [status(thm)], ['56', '57'])).
% 2.60/2.81  thf('59', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('60', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('61', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('63', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 2.60/2.81  thf('64', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         ((v2_struct_0 @ sk_A)
% 2.60/2.81          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('sup-', [status(thm)], ['55', '63'])).
% 2.60/2.81  thf('65', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 2.60/2.81         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['38', '48'])).
% 2.60/2.81  thf('66', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         ((v2_struct_0 @ sk_A)
% 2.60/2.81          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('demod', [status(thm)], ['64', '65'])).
% 2.60/2.81  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('68', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0)))),
% 2.60/2.81      inference('clc', [status(thm)], ['66', '67'])).
% 2.60/2.81  thf('69', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 2.60/2.81        | ((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81            = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 2.60/2.81               (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))))),
% 2.60/2.81      inference('sup-', [status(thm)], ['54', '68'])).
% 2.60/2.81  thf('70', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('71', plain,
% 2.60/2.81      (((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 2.60/2.81            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 2.60/2.81  thf('72', plain,
% 2.60/2.81      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 2.60/2.81        | (m1_subset_1 @ 
% 2.60/2.81           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81           (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('demod', [status(thm)], ['53', '71'])).
% 2.60/2.81  thf('73', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('74', plain,
% 2.60/2.81      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81        (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 2.60/2.81  thf('75', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf(d10_orders_2, axiom,
% 2.60/2.81    (![A:$i]:
% 2.60/2.81     ( ( l1_orders_2 @ A ) =>
% 2.60/2.81       ( ![B:$i]:
% 2.60/2.81         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.60/2.81           ( ![C:$i]:
% 2.60/2.81             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.60/2.81               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 2.60/2.81                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 2.60/2.81  thf('76', plain,
% 2.60/2.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.60/2.81          | ~ (r2_orders_2 @ X15 @ X14 @ X16)
% 2.60/2.81          | ((X14) != (X16))
% 2.60/2.81          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 2.60/2.81          | ~ (l1_orders_2 @ X15))),
% 2.60/2.81      inference('cnf', [status(esa)], [d10_orders_2])).
% 2.60/2.81  thf('77', plain,
% 2.60/2.81      (![X15 : $i, X16 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X15)
% 2.60/2.81          | ~ (r2_orders_2 @ X15 @ X16 @ X16)
% 2.60/2.81          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15)))),
% 2.60/2.81      inference('simplify', [status(thm)], ['76'])).
% 2.60/2.81  thf('78', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (r2_orders_2 @ sk_A @ X0 @ X0)
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A))),
% 2.60/2.81      inference('sup-', [status(thm)], ['75', '77'])).
% 2.60/2.81  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('80', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | ~ (r2_orders_2 @ sk_A @ X0 @ X0))),
% 2.60/2.81      inference('demod', [status(thm)], ['78', '79'])).
% 2.60/2.81  thf('81', plain,
% 2.60/2.81      (~ (r2_orders_2 @ sk_A @ 
% 2.60/2.81          (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81          (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('sup-', [status(thm)], ['74', '80'])).
% 2.60/2.81  thf('82', plain,
% 2.60/2.81      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81        (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 2.60/2.81  thf('83', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf(t4_subset_1, axiom,
% 2.60/2.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.60/2.81  thf('84', plain,
% 2.60/2.81      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 2.60/2.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.60/2.81  thf('85', plain,
% 2.60/2.81      (![X20 : $i, X21 : $i, X23 : $i, X24 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X20)
% 2.60/2.81          | ~ (v5_orders_2 @ X20)
% 2.60/2.81          | ~ (v4_orders_2 @ X20)
% 2.60/2.81          | ~ (v3_orders_2 @ X20)
% 2.60/2.81          | (v2_struct_0 @ X20)
% 2.60/2.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.60/2.81          | (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21))
% 2.60/2.81          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 2.60/2.81          | ((X23) != (X24))
% 2.60/2.81          | (r2_hidden @ (sk_E @ X24 @ X21 @ X20) @ X21))),
% 2.60/2.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.60/2.81  thf('86', plain,
% 2.60/2.81      (![X20 : $i, X21 : $i, X24 : $i]:
% 2.60/2.81         ((r2_hidden @ (sk_E @ X24 @ X21 @ X20) @ X21)
% 2.60/2.81          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X20))
% 2.60/2.81          | (r2_hidden @ X24 @ (a_2_1_orders_2 @ X20 @ X21))
% 2.60/2.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.60/2.81          | (v2_struct_0 @ X20)
% 2.60/2.81          | ~ (v3_orders_2 @ X20)
% 2.60/2.81          | ~ (v4_orders_2 @ X20)
% 2.60/2.81          | ~ (v5_orders_2 @ X20)
% 2.60/2.81          | ~ (l1_orders_2 @ X20))),
% 2.60/2.81      inference('simplify', [status(thm)], ['85'])).
% 2.60/2.81  thf('87', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X0)
% 2.60/2.81          | ~ (v5_orders_2 @ X0)
% 2.60/2.81          | ~ (v4_orders_2 @ X0)
% 2.60/2.81          | ~ (v3_orders_2 @ X0)
% 2.60/2.81          | (v2_struct_0 @ X0)
% 2.60/2.81          | (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 2.60/2.81          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.60/2.81          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['84', '86'])).
% 2.60/2.81  thf('88', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 2.60/2.81          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ k1_xboole_0))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A))),
% 2.60/2.81      inference('sup-', [status(thm)], ['83', '87'])).
% 2.60/2.81  thf('89', plain,
% 2.60/2.81      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 2.60/2.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.60/2.81  thf('90', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0))
% 2.60/2.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('clc', [status(thm)], ['46', '47'])).
% 2.60/2.81  thf('91', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ k1_xboole_0)
% 2.60/2.81         = (a_2_1_orders_2 @ sk_A @ k1_xboole_0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['89', '90'])).
% 2.60/2.81  thf('92', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 2.60/2.81      inference('clc', [status(thm)], ['18', '19'])).
% 2.60/2.81  thf('93', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('94', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['92', '93'])).
% 2.60/2.81  thf('95', plain,
% 2.60/2.81      (((k2_struct_0 @ sk_A) = (a_2_1_orders_2 @ sk_A @ k1_xboole_0))),
% 2.60/2.81      inference('demod', [status(thm)], ['91', '94'])).
% 2.60/2.81  thf('96', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('98', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('99', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('100', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 2.60/2.81          | (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['88', '95', '96', '97', '98', '99'])).
% 2.60/2.81  thf('101', plain,
% 2.60/2.81      (((v2_struct_0 @ sk_A)
% 2.60/2.81        | (r2_hidden @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81           (k2_struct_0 @ sk_A))
% 2.60/2.81        | (r2_hidden @ 
% 2.60/2.81           (sk_E @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81            k1_xboole_0 @ sk_A) @ 
% 2.60/2.81           k1_xboole_0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['82', '100'])).
% 2.60/2.81  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('103', plain,
% 2.60/2.81      (((r2_hidden @ 
% 2.60/2.81         (sk_E @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81          k1_xboole_0 @ sk_A) @ 
% 2.60/2.81         k1_xboole_0)
% 2.60/2.81        | (r2_hidden @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81           (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('clc', [status(thm)], ['101', '102'])).
% 2.60/2.81  thf(t113_zfmisc_1, axiom,
% 2.60/2.81    (![A:$i,B:$i]:
% 2.60/2.81     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.60/2.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.60/2.81  thf('104', plain,
% 2.60/2.81      (![X2 : $i, X3 : $i]:
% 2.60/2.81         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.60/2.81      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.60/2.81  thf('105', plain,
% 2.60/2.81      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 2.60/2.81      inference('simplify', [status(thm)], ['104'])).
% 2.60/2.81  thf(t152_zfmisc_1, axiom,
% 2.60/2.81    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.60/2.81  thf('106', plain,
% 2.60/2.81      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 2.60/2.81      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.60/2.81  thf('107', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.60/2.81      inference('sup-', [status(thm)], ['105', '106'])).
% 2.60/2.81  thf('108', plain,
% 2.60/2.81      ((r2_hidden @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81        (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('clc', [status(thm)], ['103', '107'])).
% 2.60/2.81  thf('109', plain,
% 2.60/2.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.60/2.81      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.60/2.81  thf('110', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('111', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 2.60/2.81      inference('demod', [status(thm)], ['1', '2'])).
% 2.60/2.81  thf('112', plain,
% 2.60/2.81      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.60/2.81         (~ (l1_orders_2 @ X20)
% 2.60/2.81          | ~ (v5_orders_2 @ X20)
% 2.60/2.81          | ~ (v4_orders_2 @ X20)
% 2.60/2.81          | ~ (v3_orders_2 @ X20)
% 2.60/2.81          | (v2_struct_0 @ X20)
% 2.60/2.81          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.60/2.81          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 2.60/2.81          | (r2_orders_2 @ X20 @ (sk_D @ X21 @ X20 @ X23) @ X22)
% 2.60/2.81          | ~ (r2_hidden @ X22 @ X21)
% 2.60/2.81          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 2.60/2.81      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.60/2.81  thf('113', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.60/2.81          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 2.60/2.81          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 2.60/2.81          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.60/2.81          | (v2_struct_0 @ X0)
% 2.60/2.81          | ~ (v3_orders_2 @ X0)
% 2.60/2.81          | ~ (v4_orders_2 @ X0)
% 2.60/2.81          | ~ (v5_orders_2 @ X0)
% 2.60/2.81          | ~ (l1_orders_2 @ X0))),
% 2.60/2.81      inference('sup-', [status(thm)], ['111', '112'])).
% 2.60/2.81  thf('114', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | ~ (l1_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v5_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v4_orders_2 @ sk_A)
% 2.60/2.81          | ~ (v3_orders_2 @ sk_A)
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 2.60/2.81          | (r2_orders_2 @ sk_A @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 2.60/2.81             X1)
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['110', '113'])).
% 2.60/2.81  thf('115', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 2.60/2.81         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('sup-', [status(thm)], ['38', '48'])).
% 2.60/2.81  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('117', plain, ((v5_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('118', plain, ((v4_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('119', plain, ((v3_orders_2 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('120', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('121', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('122', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 2.60/2.81  thf('123', plain,
% 2.60/2.81      (![X0 : $i, X1 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81          | (v2_struct_0 @ sk_A)
% 2.60/2.81          | ~ (m1_subset_1 @ X1 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_orders_2 @ sk_A @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 2.60/2.81             X1)
% 2.60/2.81          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ sk_A)))),
% 2.60/2.81      inference('demod', [status(thm)],
% 2.60/2.81                ['114', '115', '116', '117', '118', '119', '120', '121', '122'])).
% 2.60/2.81  thf('124', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_orders_2 @ sk_A @ 
% 2.60/2.81             (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 2.60/2.81              (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 2.60/2.81             X0)
% 2.60/2.81          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('sup-', [status(thm)], ['109', '123'])).
% 2.60/2.81  thf('125', plain,
% 2.60/2.81      (((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 2.60/2.81         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 2.60/2.81            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 2.60/2.81  thf('126', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 2.60/2.81          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_orders_2 @ sk_A @ 
% 2.60/2.81             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 2.60/2.81          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('demod', [status(thm)], ['124', '125'])).
% 2.60/2.81  thf('127', plain,
% 2.60/2.81      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('128', plain,
% 2.60/2.81      (![X0 : $i]:
% 2.60/2.81         (~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (r2_orders_2 @ sk_A @ 
% 2.60/2.81             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 2.60/2.81          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 2.60/2.81          | (v2_struct_0 @ sk_A))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 2.60/2.81  thf('129', plain,
% 2.60/2.81      (((v2_struct_0 @ sk_A)
% 2.60/2.81        | ~ (m1_subset_1 @ 
% 2.60/2.81             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81             (k2_struct_0 @ sk_A))
% 2.60/2.81        | (r2_orders_2 @ sk_A @ 
% 2.60/2.81           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 2.60/2.81      inference('sup-', [status(thm)], ['108', '128'])).
% 2.60/2.81  thf('130', plain,
% 2.60/2.81      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81        (k2_struct_0 @ sk_A))),
% 2.60/2.81      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 2.60/2.81  thf('131', plain,
% 2.60/2.81      (((v2_struct_0 @ sk_A)
% 2.60/2.81        | (r2_orders_2 @ sk_A @ 
% 2.60/2.81           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 2.60/2.81      inference('demod', [status(thm)], ['129', '130'])).
% 2.60/2.81  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 2.60/2.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.60/2.81  thf('133', plain,
% 2.60/2.81      ((r2_orders_2 @ sk_A @ 
% 2.60/2.81        (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 2.60/2.81        (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 2.60/2.81      inference('clc', [status(thm)], ['131', '132'])).
% 2.60/2.81  thf('134', plain, ($false), inference('demod', [status(thm)], ['81', '133'])).
% 2.60/2.81  
% 2.60/2.81  % SZS output end Refutation
% 2.60/2.81  
% 2.60/2.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
