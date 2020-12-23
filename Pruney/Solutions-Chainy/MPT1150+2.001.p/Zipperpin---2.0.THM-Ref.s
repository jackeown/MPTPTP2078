%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGkwB0epKy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:38 EST 2020

% Result     : Theorem 8.57s
% Output     : Refutation 8.57s
% Verified   : 
% Statistics : Number of formulae       :  167 (2721 expanded)
%              Number of leaves         :   37 ( 835 expanded)
%              Depth                    :   27
%              Number of atoms          : 1438 (27609 expanded)
%              Number of equality atoms :   69 (1828 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t44_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_orders_2])).

thf('1',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ( ( k1_struct_0 @ X16 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('5',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t43_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X29: $i] :
      ( ( ( k1_orders_2 @ X29 @ ( k1_struct_0 @ X29 ) )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_orders_2])).

thf('7',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('13',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('17',plain,
    ( ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('19',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fraenkel_a_2_0_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ E @ D ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X24 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ ( a_2_0_orders_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('29',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(d12_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_orders_2 @ A @ B )
            = ( a_2_0_orders_2 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_orders_2 @ X22 @ X21 )
        = ( a_2_0_orders_2 @ X22 @ X21 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

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
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','39','40','41','42','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('52',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('53',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X27
        = ( sk_D @ X25 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ ( a_2_0_orders_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','64'])).

thf('66',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','67'])).

thf('69',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

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

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_orders_2 @ X19 @ X18 @ X20 )
      | ( X18 != X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( r2_orders_2 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('80',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('82',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ( r2_orders_2 @ X24 @ X26 @ ( sk_D @ X25 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( a_2_0_orders_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( a_2_0_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( a_2_0_orders_2 @ sk_A @ ( u1_struct_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('87',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('88',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('89',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('90',plain,
    ( ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('96',plain,
    ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89','90','91','92','93','94','95','96'])).

thf('98',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ X0 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('102',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('103',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('104',plain,(
    ! [X24: $i,X25: $i,X27: $i,X28: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r2_hidden @ X27 @ ( a_2_0_orders_2 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ( X27 != X28 )
      | ( r2_hidden @ ( sk_E @ X28 @ X25 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('105',plain,(
    ! [X24: $i,X25: $i,X28: $i] :
      ( ( r2_hidden @ ( sk_E @ X28 @ X25 @ X24 ) @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ( r2_hidden @ X28 @ ( a_2_0_orders_2 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v2_struct_0 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( l1_orders_2 @ X24 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ sk_A @ X0 )
        = ( a_2_0_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('110',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('112',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( a_2_0_orders_2 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','112','113','114','115','116'])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('121',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('122',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('123',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('124',plain,(
    r2_hidden @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    r2_orders_2 @ sk_A @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    $false ),
    inference(demod,[status(thm)],['77','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NGkwB0epKy
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.57/8.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.57/8.74  % Solved by: fo/fo7.sh
% 8.57/8.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.57/8.74  % done 11476 iterations in 8.283s
% 8.57/8.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.57/8.74  % SZS output start Refutation
% 8.57/8.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.57/8.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 8.57/8.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.57/8.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 8.57/8.74  thf(sk_A_type, type, sk_A: $i).
% 8.57/8.74  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 8.57/8.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.57/8.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.57/8.74  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 8.57/8.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.57/8.74  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 8.57/8.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.57/8.74  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 8.57/8.74  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 8.57/8.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.57/8.74  thf(sk_B_type, type, sk_B: $i > $i).
% 8.57/8.74  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 8.57/8.74  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 8.57/8.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.57/8.74  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 8.57/8.74  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 8.57/8.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.57/8.74  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 8.57/8.74  thf(t9_mcart_1, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 8.57/8.74          ( ![B:$i]:
% 8.57/8.74            ( ~( ( r2_hidden @ B @ A ) & 
% 8.57/8.74                 ( ![C:$i,D:$i]:
% 8.57/8.74                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 8.57/8.74                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 8.57/8.74  thf('0', plain,
% 8.57/8.74      (![X13 : $i]:
% 8.57/8.74         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 8.57/8.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 8.57/8.74  thf(t44_orders_2, conjecture,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.57/8.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.57/8.74       ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 8.57/8.74  thf(zf_stmt_0, negated_conjecture,
% 8.57/8.74    (~( ![A:$i]:
% 8.57/8.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.57/8.74            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.57/8.74          ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 8.57/8.74    inference('cnf.neg', [status(esa)], [t44_orders_2])).
% 8.57/8.74  thf('1', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf(dt_l1_orders_2, axiom,
% 8.57/8.74    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 8.57/8.74  thf('2', plain, (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_orders_2 @ X23))),
% 8.57/8.74      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 8.57/8.74  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 8.57/8.74      inference('sup-', [status(thm)], ['1', '2'])).
% 8.57/8.74  thf(d2_struct_0, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 8.57/8.74  thf('4', plain,
% 8.57/8.74      (![X16 : $i]:
% 8.57/8.74         (((k1_struct_0 @ X16) = (k1_xboole_0)) | ~ (l1_struct_0 @ X16))),
% 8.57/8.74      inference('cnf', [status(esa)], [d2_struct_0])).
% 8.57/8.74  thf('5', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['3', '4'])).
% 8.57/8.74  thf(t43_orders_2, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.57/8.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.57/8.74       ( ( k1_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 8.57/8.74  thf('6', plain,
% 8.57/8.74      (![X29 : $i]:
% 8.57/8.74         (((k1_orders_2 @ X29 @ (k1_struct_0 @ X29)) = (u1_struct_0 @ X29))
% 8.57/8.74          | ~ (l1_orders_2 @ X29)
% 8.57/8.74          | ~ (v5_orders_2 @ X29)
% 8.57/8.74          | ~ (v4_orders_2 @ X29)
% 8.57/8.74          | ~ (v3_orders_2 @ X29)
% 8.57/8.74          | (v2_struct_0 @ X29))),
% 8.57/8.74      inference('cnf', [status(esa)], [t43_orders_2])).
% 8.57/8.74  thf('7', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 8.57/8.74        | (v2_struct_0 @ sk_A)
% 8.57/8.74        | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74        | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74        | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74        | ~ (l1_orders_2 @ sk_A))),
% 8.57/8.74      inference('sup+', [status(thm)], ['5', '6'])).
% 8.57/8.74  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('10', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('11', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('12', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 8.57/8.74        | (v2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 8.57/8.74  thf('13', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('14', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('clc', [status(thm)], ['12', '13'])).
% 8.57/8.74  thf(d3_struct_0, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 8.57/8.74  thf('15', plain,
% 8.57/8.74      (![X17 : $i]:
% 8.57/8.74         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 8.57/8.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.57/8.74  thf('16', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('clc', [status(thm)], ['12', '13'])).
% 8.57/8.74  thf('17', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))
% 8.57/8.74        | ~ (l1_struct_0 @ sk_A))),
% 8.57/8.74      inference('sup+', [status(thm)], ['15', '16'])).
% 8.57/8.74  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 8.57/8.74      inference('sup-', [status(thm)], ['1', '2'])).
% 8.57/8.74  thf('19', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['17', '18'])).
% 8.57/8.74  thf('20', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf(d10_xboole_0, axiom,
% 8.57/8.74    (![A:$i,B:$i]:
% 8.57/8.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.57/8.74  thf('21', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.57/8.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.57/8.74  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.57/8.74      inference('simplify', [status(thm)], ['21'])).
% 8.57/8.74  thf(t3_subset, axiom,
% 8.57/8.74    (![A:$i,B:$i]:
% 8.57/8.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.57/8.74  thf('23', plain,
% 8.57/8.74      (![X5 : $i, X7 : $i]:
% 8.57/8.74         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 8.57/8.74      inference('cnf', [status(esa)], [t3_subset])).
% 8.57/8.74  thf('24', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['22', '23'])).
% 8.57/8.74  thf(fraenkel_a_2_0_orders_2, axiom,
% 8.57/8.74    (![A:$i,B:$i,C:$i]:
% 8.57/8.74     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 8.57/8.74         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 8.57/8.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 8.57/8.74       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 8.57/8.74         ( ?[D:$i]:
% 8.57/8.74           ( ( ![E:$i]:
% 8.57/8.74               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 8.57/8.74                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 8.57/8.74             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.57/8.74  thf('25', plain,
% 8.57/8.74      (![X24 : $i, X25 : $i, X27 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X24)
% 8.57/8.74          | ~ (v5_orders_2 @ X24)
% 8.57/8.74          | ~ (v4_orders_2 @ X24)
% 8.57/8.74          | ~ (v3_orders_2 @ X24)
% 8.57/8.74          | (v2_struct_0 @ X24)
% 8.57/8.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.57/8.74          | (m1_subset_1 @ (sk_D @ X25 @ X24 @ X27) @ (u1_struct_0 @ X24))
% 8.57/8.74          | ~ (r2_hidden @ X27 @ (a_2_0_orders_2 @ X24 @ X25)))),
% 8.57/8.74      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 8.57/8.74  thf('26', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 8.57/8.74          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 8.57/8.74             (u1_struct_0 @ X0))
% 8.57/8.74          | (v2_struct_0 @ X0)
% 8.57/8.74          | ~ (v3_orders_2 @ X0)
% 8.57/8.74          | ~ (v4_orders_2 @ X0)
% 8.57/8.74          | ~ (v5_orders_2 @ X0)
% 8.57/8.74          | ~ (l1_orders_2 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['24', '25'])).
% 8.57/8.74  thf('27', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 8.57/8.74             (u1_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['20', '26'])).
% 8.57/8.74  thf('28', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['22', '23'])).
% 8.57/8.74  thf('29', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf(d12_orders_2, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.57/8.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.57/8.74       ( ![B:$i]:
% 8.57/8.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.57/8.74           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 8.57/8.74  thf('30', plain,
% 8.57/8.74      (![X21 : $i, X22 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 8.57/8.74          | ((k1_orders_2 @ X22 @ X21) = (a_2_0_orders_2 @ X22 @ X21))
% 8.57/8.74          | ~ (l1_orders_2 @ X22)
% 8.57/8.74          | ~ (v5_orders_2 @ X22)
% 8.57/8.74          | ~ (v4_orders_2 @ X22)
% 8.57/8.74          | ~ (v3_orders_2 @ X22)
% 8.57/8.74          | (v2_struct_0 @ X22))),
% 8.57/8.74      inference('cnf', [status(esa)], [d12_orders_2])).
% 8.57/8.74  thf('31', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A)
% 8.57/8.74          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['29', '30'])).
% 8.57/8.74  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('36', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0)))),
% 8.57/8.74      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 8.57/8.74  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('38', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 8.57/8.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('clc', [status(thm)], ['36', '37'])).
% 8.57/8.74  thf('39', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 8.57/8.74         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['28', '38'])).
% 8.57/8.74  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('42', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('43', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('44', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('45', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('46', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 8.57/8.74             (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('demod', [status(thm)],
% 8.57/8.74                ['27', '39', '40', '41', '42', '43', '44', '45'])).
% 8.57/8.74  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('48', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 8.57/8.74           (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('clc', [status(thm)], ['46', '47'])).
% 8.57/8.74  thf('49', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 8.57/8.74        | (m1_subset_1 @ 
% 8.57/8.74           (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 8.57/8.74            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 8.57/8.74           (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['0', '48'])).
% 8.57/8.74  thf('50', plain,
% 8.57/8.74      (![X13 : $i]:
% 8.57/8.74         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 8.57/8.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 8.57/8.74  thf('51', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['22', '23'])).
% 8.57/8.74  thf('52', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('53', plain,
% 8.57/8.74      (![X24 : $i, X25 : $i, X27 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X24)
% 8.57/8.74          | ~ (v5_orders_2 @ X24)
% 8.57/8.74          | ~ (v4_orders_2 @ X24)
% 8.57/8.74          | ~ (v3_orders_2 @ X24)
% 8.57/8.74          | (v2_struct_0 @ X24)
% 8.57/8.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.57/8.74          | ((X27) = (sk_D @ X25 @ X24 @ X27))
% 8.57/8.74          | ~ (r2_hidden @ X27 @ (a_2_0_orders_2 @ X24 @ X25)))),
% 8.57/8.74      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 8.57/8.74  thf('54', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 8.57/8.74          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A))),
% 8.57/8.74      inference('sup-', [status(thm)], ['52', '53'])).
% 8.57/8.74  thf('55', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('56', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('58', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('59', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ sk_A @ X0))
% 8.57/8.74          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 8.57/8.74          | (v2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 8.57/8.74  thf('60', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         ((v2_struct_0 @ sk_A)
% 8.57/8.74          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('sup-', [status(thm)], ['51', '59'])).
% 8.57/8.74  thf('61', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 8.57/8.74         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['28', '38'])).
% 8.57/8.74  thf('62', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         ((v2_struct_0 @ sk_A)
% 8.57/8.74          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('demod', [status(thm)], ['60', '61'])).
% 8.57/8.74  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('64', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0)))),
% 8.57/8.74      inference('clc', [status(thm)], ['62', '63'])).
% 8.57/8.74  thf('65', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 8.57/8.74        | ((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74            = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 8.57/8.74               (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))))),
% 8.57/8.74      inference('sup-', [status(thm)], ['50', '64'])).
% 8.57/8.74  thf('66', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('67', plain,
% 8.57/8.74      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 8.57/8.74            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 8.57/8.74  thf('68', plain,
% 8.57/8.74      ((((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 8.57/8.74        | (m1_subset_1 @ 
% 8.57/8.74           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74           (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('demod', [status(thm)], ['49', '67'])).
% 8.57/8.74  thf('69', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('70', plain,
% 8.57/8.74      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74        (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 8.57/8.74  thf('71', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf(d10_orders_2, axiom,
% 8.57/8.74    (![A:$i]:
% 8.57/8.74     ( ( l1_orders_2 @ A ) =>
% 8.57/8.74       ( ![B:$i]:
% 8.57/8.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.57/8.74           ( ![C:$i]:
% 8.57/8.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 8.57/8.74               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 8.57/8.74                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 8.57/8.74  thf('72', plain,
% 8.57/8.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 8.57/8.74          | ~ (r2_orders_2 @ X19 @ X18 @ X20)
% 8.57/8.74          | ((X18) != (X20))
% 8.57/8.74          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 8.57/8.74          | ~ (l1_orders_2 @ X19))),
% 8.57/8.74      inference('cnf', [status(esa)], [d10_orders_2])).
% 8.57/8.74  thf('73', plain,
% 8.57/8.74      (![X19 : $i, X20 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X19)
% 8.57/8.74          | ~ (r2_orders_2 @ X19 @ X20 @ X20)
% 8.57/8.74          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19)))),
% 8.57/8.74      inference('simplify', [status(thm)], ['72'])).
% 8.57/8.74  thf('74', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_orders_2 @ sk_A @ X0 @ X0)
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A))),
% 8.57/8.74      inference('sup-', [status(thm)], ['71', '73'])).
% 8.57/8.74  thf('75', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('76', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_orders_2 @ sk_A @ X0 @ X0))),
% 8.57/8.74      inference('demod', [status(thm)], ['74', '75'])).
% 8.57/8.74  thf('77', plain,
% 8.57/8.74      (~ (r2_orders_2 @ sk_A @ 
% 8.57/8.74          (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74          (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('sup-', [status(thm)], ['70', '76'])).
% 8.57/8.74  thf('78', plain,
% 8.57/8.74      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74        (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 8.57/8.74  thf('79', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('80', plain,
% 8.57/8.74      (![X13 : $i]:
% 8.57/8.74         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X13) @ X13))),
% 8.57/8.74      inference('cnf', [status(esa)], [t9_mcart_1])).
% 8.57/8.74  thf('81', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['22', '23'])).
% 8.57/8.74  thf('82', plain,
% 8.57/8.74      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X24)
% 8.57/8.74          | ~ (v5_orders_2 @ X24)
% 8.57/8.74          | ~ (v4_orders_2 @ X24)
% 8.57/8.74          | ~ (v3_orders_2 @ X24)
% 8.57/8.74          | (v2_struct_0 @ X24)
% 8.57/8.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.57/8.74          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 8.57/8.74          | (r2_orders_2 @ X24 @ X26 @ (sk_D @ X25 @ X24 @ X27))
% 8.57/8.74          | ~ (r2_hidden @ X26 @ X25)
% 8.57/8.74          | ~ (r2_hidden @ X27 @ (a_2_0_orders_2 @ X24 @ X25)))),
% 8.57/8.74      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 8.57/8.74  thf('83', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 8.57/8.74          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 8.57/8.74          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 8.57/8.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.57/8.74          | (v2_struct_0 @ X0)
% 8.57/8.74          | ~ (v3_orders_2 @ X0)
% 8.57/8.74          | ~ (v4_orders_2 @ X0)
% 8.57/8.74          | ~ (v5_orders_2 @ X0)
% 8.57/8.74          | ~ (l1_orders_2 @ X0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['81', '82'])).
% 8.57/8.74  thf('84', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]:
% 8.57/8.74         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 8.57/8.74          | ~ (l1_orders_2 @ X0)
% 8.57/8.74          | ~ (v5_orders_2 @ X0)
% 8.57/8.74          | ~ (v4_orders_2 @ X0)
% 8.57/8.74          | ~ (v3_orders_2 @ X0)
% 8.57/8.74          | (v2_struct_0 @ X0)
% 8.57/8.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 8.57/8.74          | (r2_orders_2 @ X0 @ X1 @ 
% 8.57/8.74             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 8.57/8.74              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 8.57/8.74          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['80', '83'])).
% 8.57/8.74  thf('85', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 8.57/8.74          | (r2_orders_2 @ sk_A @ X0 @ 
% 8.57/8.74             (sk_D @ (u1_struct_0 @ sk_A) @ sk_A @ 
% 8.57/8.74              (sk_B @ (a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)))))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A)
% 8.57/8.74          | ((a_2_0_orders_2 @ sk_A @ (u1_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['79', '84'])).
% 8.57/8.74  thf('86', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('87', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('88', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('89', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 8.57/8.74         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['28', '38'])).
% 8.57/8.74  thf('90', plain,
% 8.57/8.74      (((sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 8.57/8.74         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 8.57/8.74            (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 8.57/8.74  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('95', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf('96', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 8.57/8.74         = (a_2_0_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['28', '38'])).
% 8.57/8.74  thf('97', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | (r2_orders_2 @ sk_A @ X0 @ 
% 8.57/8.74             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 8.57/8.74      inference('demod', [status(thm)],
% 8.57/8.74                ['85', '86', '87', '88', '89', '90', '91', '92', '93', '94', 
% 8.57/8.74                 '95', '96'])).
% 8.57/8.74  thf('98', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('99', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | (r2_orders_2 @ sk_A @ X0 @ 
% 8.57/8.74             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 8.57/8.74          | (v2_struct_0 @ sk_A))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 8.57/8.74  thf('100', plain,
% 8.57/8.74      (((v2_struct_0 @ sk_A)
% 8.57/8.74        | (r2_orders_2 @ sk_A @ 
% 8.57/8.74           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 8.57/8.74        | ~ (r2_hidden @ 
% 8.57/8.74             (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74             (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['78', '99'])).
% 8.57/8.74  thf('101', plain,
% 8.57/8.74      ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74        (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 8.57/8.74  thf('102', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['14', '19'])).
% 8.57/8.74  thf(t4_subset_1, axiom,
% 8.57/8.74    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 8.57/8.74  thf('103', plain,
% 8.57/8.74      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 8.57/8.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.57/8.74  thf('104', plain,
% 8.57/8.74      (![X24 : $i, X25 : $i, X27 : $i, X28 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X24)
% 8.57/8.74          | ~ (v5_orders_2 @ X24)
% 8.57/8.74          | ~ (v4_orders_2 @ X24)
% 8.57/8.74          | ~ (v3_orders_2 @ X24)
% 8.57/8.74          | (v2_struct_0 @ X24)
% 8.57/8.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.57/8.74          | (r2_hidden @ X27 @ (a_2_0_orders_2 @ X24 @ X25))
% 8.57/8.74          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 8.57/8.74          | ((X27) != (X28))
% 8.57/8.74          | (r2_hidden @ (sk_E @ X28 @ X25 @ X24) @ X25))),
% 8.57/8.74      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 8.57/8.74  thf('105', plain,
% 8.57/8.74      (![X24 : $i, X25 : $i, X28 : $i]:
% 8.57/8.74         ((r2_hidden @ (sk_E @ X28 @ X25 @ X24) @ X25)
% 8.57/8.74          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 8.57/8.74          | (r2_hidden @ X28 @ (a_2_0_orders_2 @ X24 @ X25))
% 8.57/8.74          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 8.57/8.74          | (v2_struct_0 @ X24)
% 8.57/8.74          | ~ (v3_orders_2 @ X24)
% 8.57/8.74          | ~ (v4_orders_2 @ X24)
% 8.57/8.74          | ~ (v5_orders_2 @ X24)
% 8.57/8.74          | ~ (l1_orders_2 @ X24))),
% 8.57/8.74      inference('simplify', [status(thm)], ['104'])).
% 8.57/8.74  thf('106', plain,
% 8.57/8.74      (![X0 : $i, X1 : $i]:
% 8.57/8.74         (~ (l1_orders_2 @ X0)
% 8.57/8.74          | ~ (v5_orders_2 @ X0)
% 8.57/8.74          | ~ (v4_orders_2 @ X0)
% 8.57/8.74          | ~ (v3_orders_2 @ X0)
% 8.57/8.74          | (v2_struct_0 @ X0)
% 8.57/8.74          | (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ k1_xboole_0))
% 8.57/8.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 8.57/8.74          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['103', '105'])).
% 8.57/8.74  thf('107', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 8.57/8.74          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ k1_xboole_0))
% 8.57/8.74          | (v2_struct_0 @ sk_A)
% 8.57/8.74          | ~ (v3_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v4_orders_2 @ sk_A)
% 8.57/8.74          | ~ (v5_orders_2 @ sk_A)
% 8.57/8.74          | ~ (l1_orders_2 @ sk_A))),
% 8.57/8.74      inference('sup-', [status(thm)], ['102', '106'])).
% 8.57/8.74  thf('108', plain,
% 8.57/8.74      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 8.57/8.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.57/8.74  thf('109', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (((k1_orders_2 @ sk_A @ X0) = (a_2_0_orders_2 @ sk_A @ X0))
% 8.57/8.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('clc', [status(thm)], ['36', '37'])).
% 8.57/8.74  thf('110', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ k1_xboole_0)
% 8.57/8.74         = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['108', '109'])).
% 8.57/8.74  thf('111', plain,
% 8.57/8.74      (((k1_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['17', '18'])).
% 8.57/8.74  thf('112', plain,
% 8.57/8.74      (((k2_struct_0 @ sk_A) = (a_2_0_orders_2 @ sk_A @ k1_xboole_0))),
% 8.57/8.74      inference('demod', [status(thm)], ['110', '111'])).
% 8.57/8.74  thf('113', plain, ((v3_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('114', plain, ((v4_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('115', plain, ((v5_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('116', plain, ((l1_orders_2 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('117', plain,
% 8.57/8.74      (![X0 : $i]:
% 8.57/8.74         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | (r2_hidden @ (sk_E @ X0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 8.57/8.74          | (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 8.57/8.74          | (v2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)],
% 8.57/8.74                ['107', '112', '113', '114', '115', '116'])).
% 8.57/8.74  thf('118', plain,
% 8.57/8.74      (((v2_struct_0 @ sk_A)
% 8.57/8.74        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74           (k2_struct_0 @ sk_A))
% 8.57/8.74        | (r2_hidden @ 
% 8.57/8.74           (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74            k1_xboole_0 @ sk_A) @ 
% 8.57/8.74           k1_xboole_0))),
% 8.57/8.74      inference('sup-', [status(thm)], ['101', '117'])).
% 8.57/8.74  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('120', plain,
% 8.57/8.74      (((r2_hidden @ 
% 8.57/8.74         (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74          k1_xboole_0 @ sk_A) @ 
% 8.57/8.74         k1_xboole_0)
% 8.57/8.74        | (r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74           (k2_struct_0 @ sk_A)))),
% 8.57/8.74      inference('clc', [status(thm)], ['118', '119'])).
% 8.57/8.74  thf(t7_ordinal1, axiom,
% 8.57/8.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.57/8.74  thf('121', plain,
% 8.57/8.74      (![X11 : $i, X12 : $i]:
% 8.57/8.74         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 8.57/8.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 8.57/8.74  thf('122', plain,
% 8.57/8.74      (((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74         (k2_struct_0 @ sk_A))
% 8.57/8.74        | ~ (r1_tarski @ k1_xboole_0 @ 
% 8.57/8.74             (sk_E @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74              k1_xboole_0 @ sk_A)))),
% 8.57/8.74      inference('sup-', [status(thm)], ['120', '121'])).
% 8.57/8.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.57/8.74  thf('123', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 8.57/8.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.57/8.74  thf('124', plain,
% 8.57/8.74      ((r2_hidden @ (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74        (k2_struct_0 @ sk_A))),
% 8.57/8.74      inference('demod', [status(thm)], ['122', '123'])).
% 8.57/8.74  thf('125', plain,
% 8.57/8.74      (((v2_struct_0 @ sk_A)
% 8.57/8.74        | (r2_orders_2 @ sk_A @ 
% 8.57/8.74           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74           (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 8.57/8.74      inference('demod', [status(thm)], ['100', '124'])).
% 8.57/8.74  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 8.57/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.57/8.74  thf('127', plain,
% 8.57/8.74      ((r2_orders_2 @ sk_A @ 
% 8.57/8.74        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 8.57/8.74        (sk_B @ (k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 8.57/8.74      inference('clc', [status(thm)], ['125', '126'])).
% 8.57/8.74  thf('128', plain, ($false), inference('demod', [status(thm)], ['77', '127'])).
% 8.57/8.74  
% 8.57/8.74  % SZS output end Refutation
% 8.57/8.74  
% 8.57/8.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
