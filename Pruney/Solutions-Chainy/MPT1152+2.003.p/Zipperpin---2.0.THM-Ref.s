%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8C8vcEFixd

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:42 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  163 (5297 expanded)
%              Number of leaves         :   33 (1606 expanded)
%              Depth                    :   29
%              Number of atoms          : 1373 (53420 expanded)
%              Number of equality atoms :   65 (3478 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('0',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('10',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t45_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( ( ( k2_orders_2 @ X23 @ ( k1_struct_0 @ X23 ) )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v4_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_orders_2])).

thf('12',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('22',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('24',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

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

thf('26',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X19 @ X18 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_A @ X1 ) @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['5','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('36',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

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

thf('42',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_orders_2 @ X16 @ X15 )
        = ( a_2_1_orders_2 @ X16 @ X15 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ X0 )
        = ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['34','35','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X21
        = ( sk_D @ X19 @ X18 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('60',plain,(
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
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ( X1
        = ( sk_D @ X0 @ sk_A @ X1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('68',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      | ( X0
        = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
      = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','74'])).

thf('76',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('82',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( r2_orders_2 @ X18 @ ( sk_D @ X19 @ X18 @ X21 ) @ X20 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ X0 @ sk_A @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('86',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ X0 @ sk_A @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('93',plain,
    ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','94'])).

thf('96',plain,
    ( ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) )
    = ( sk_D @ ( k2_struct_0 @ sk_A ) @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','99'])).

thf('101',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['75','76'])).

thf('106',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','24'])).

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

thf('107',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_orders_2 @ X13 @ X12 @ X14 )
      | ( X12 != X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('108',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( r2_orders_2 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( r2_orders_2 @ sk_A @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) @ ( sk_B @ ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('115',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('117',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('124',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('126',plain,
    ( ( k2_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','123'])).

thf('127',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','124','125','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8C8vcEFixd
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:22:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 124 iterations in 0.093s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.37/0.56  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.37/0.56  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.37/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.37/0.56  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.37/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(t46_orders_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.56       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.56          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t7_xboole_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf(d3_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X10 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf(dt_k2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) =>
% 0.37/0.56       ( m1_subset_1 @
% 0.37/0.56         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | ~ (l1_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | ~ (l1_struct_0 @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X0)
% 0.37/0.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.56  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_l1_orders_2, axiom,
% 0.37/0.56    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.56  thf('7', plain, (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.37/0.56  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf(d2_struct_0, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X9 : $i]:
% 0.37/0.56         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.37/0.56  thf('10', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf(t45_orders_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.56       ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X23 : $i]:
% 0.37/0.56         (((k2_orders_2 @ X23 @ (k1_struct_0 @ X23)) = (u1_struct_0 @ X23))
% 0.37/0.56          | ~ (l1_orders_2 @ X23)
% 0.37/0.56          | ~ (v5_orders_2 @ X23)
% 0.37/0.56          | ~ (v4_orders_2 @ X23)
% 0.37/0.56          | ~ (v3_orders_2 @ X23)
% 0.37/0.56          | (v2_struct_0 @ X23))),
% 0.37/0.56      inference('cnf', [status(esa)], [t45_orders_2])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (v3_orders_2 @ sk_A)
% 0.37/0.56        | ~ (v4_orders_2 @ sk_A)
% 0.37/0.56        | ~ (v5_orders_2 @ sk_A)
% 0.37/0.56        | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.37/0.56  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X10 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['17', '18'])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['20', '21'])).
% 0.37/0.56  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.37/0.56         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.37/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.56       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.37/0.56         ( ?[D:$i]:
% 0.37/0.56           ( ( ![E:$i]:
% 0.37/0.56               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.37/0.56                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.37/0.56             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.37/0.56         (~ (l1_orders_2 @ X18)
% 0.37/0.56          | ~ (v5_orders_2 @ X18)
% 0.37/0.56          | ~ (v4_orders_2 @ X18)
% 0.37/0.56          | ~ (v3_orders_2 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ X19 @ X18 @ X21) @ (u1_struct_0 @ X18))
% 0.37/0.56          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('31', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_A @ X1) @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['27', '28', '29', '30', '31', '32'])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 0.37/0.56             (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '33'])).
% 0.37/0.56  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('36', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | ~ (l1_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup+', [status(thm)], ['36', '37'])).
% 0.37/0.56  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      ((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.56  thf('41', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf(d13_orders_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.37/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.37/0.56  thf('42', plain,
% 0.37/0.56      (![X15 : $i, X16 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.56          | ((k2_orders_2 @ X16 @ X15) = (a_2_1_orders_2 @ X16 @ X15))
% 0.37/0.56          | ~ (l1_orders_2 @ X16)
% 0.37/0.56          | ~ (v5_orders_2 @ X16)
% 0.37/0.56          | ~ (v4_orders_2 @ X16)
% 0.37/0.56          | ~ (v3_orders_2 @ X16)
% 0.37/0.56          | (v2_struct_0 @ X16))),
% 0.37/0.56      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.37/0.56          | ((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.56  thf('44', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('45', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('46', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.37/0.56  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_orders_2 @ sk_A @ X0) = (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('clc', [status(thm)], ['48', '49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.56         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['40', '50'])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_A)
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 0.37/0.56             (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['34', '35', '51'])).
% 0.37/0.56  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0) @ 
% 0.37/0.56             (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['52', '53'])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ 
% 0.37/0.56           (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 0.37/0.56            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.56           (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '54'])).
% 0.37/0.56  thf('56', plain,
% 0.37/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X0)
% 0.37/0.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.56  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf('59', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.37/0.56         (~ (l1_orders_2 @ X18)
% 0.37/0.56          | ~ (v5_orders_2 @ X18)
% 0.37/0.56          | ~ (v4_orders_2 @ X18)
% 0.37/0.56          | ~ (v3_orders_2 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | ((X21) = (sk_D @ X19 @ X18 @ X21))
% 0.37/0.56          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.37/0.56  thf('60', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.56  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('65', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | ((X1) = (sk_D @ X0 @ sk_A @ X1))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.37/0.56  thf('66', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['57', '65'])).
% 0.37/0.56  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('68', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.56         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['40', '50'])).
% 0.37/0.56  thf('69', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_A)
% 0.37/0.56          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.37/0.56  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('71', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ((X0) = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X0)))),
% 0.37/0.56      inference('clc', [status(thm)], ['69', '70'])).
% 0.37/0.56  thf('72', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 0.37/0.56        | ((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.56            = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 0.37/0.56               (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['56', '71'])).
% 0.37/0.56  thf('73', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('74', plain,
% 0.37/0.56      (((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.56         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 0.37/0.56            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.37/0.56  thf('75', plain,
% 0.37/0.56      ((((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 0.37/0.56        | (m1_subset_1 @ 
% 0.37/0.56           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56           (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['55', '74'])).
% 0.37/0.56  thf('76', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('77', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56        (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf(t2_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.37/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.37/0.56  thf('78', plain,
% 0.37/0.56      (![X1 : $i, X2 : $i]:
% 0.37/0.56         ((r2_hidden @ X1 @ X2)
% 0.37/0.56          | (v1_xboole_0 @ X2)
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.37/0.56  thf('79', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | (r2_hidden @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56           (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.37/0.56  thf('80', plain,
% 0.37/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf('81', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X0)
% 0.37/0.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.37/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.56  thf('82', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf('83', plain,
% 0.37/0.56      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.56         (~ (l1_orders_2 @ X18)
% 0.37/0.56          | ~ (v5_orders_2 @ X18)
% 0.37/0.56          | ~ (v4_orders_2 @ X18)
% 0.37/0.56          | ~ (v3_orders_2 @ X18)
% 0.37/0.56          | (v2_struct_0 @ X18)
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.37/0.56          | (r2_orders_2 @ X18 @ (sk_D @ X19 @ X18 @ X21) @ X20)
% 0.37/0.56          | ~ (r2_hidden @ X20 @ X19)
% 0.37/0.56          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.37/0.56      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.37/0.56  thf('84', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X2 @ X0)
% 0.37/0.56          | (r2_orders_2 @ sk_A @ (sk_D @ X0 @ sk_A @ X1) @ X2)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.37/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.37/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.37/0.56  thf('85', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf('86', plain, ((v3_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('87', plain, ((v4_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('88', plain, ((v5_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('90', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X2 @ X0)
% 0.37/0.56          | (r2_orders_2 @ sk_A @ (sk_D @ X0 @ sk_A @ X1) @ X2)
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '89'])).
% 0.37/0.56  thf('91', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ sk_A)
% 0.37/0.56          | (v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (r2_orders_2 @ sk_A @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X1) @ 
% 0.37/0.56             X0)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['81', '90'])).
% 0.37/0.56  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('93', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.37/0.56         = (a_2_1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['40', '50'])).
% 0.37/0.56  thf('94', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((v2_struct_0 @ sk_A)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (r2_orders_2 @ sk_A @ (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ X1) @ 
% 0.37/0.56             X0)
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.37/0.56  thf('95', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (r2_orders_2 @ sk_A @ 
% 0.37/0.56             (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 0.37/0.56              (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))) @ 
% 0.37/0.56             X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['80', '94'])).
% 0.37/0.56  thf('96', plain,
% 0.37/0.56      (((sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))
% 0.37/0.56         = (sk_D @ (k2_struct_0 @ sk_A) @ sk_A @ 
% 0.37/0.56            (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.37/0.56  thf('97', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0))
% 0.37/0.56          | ~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (r2_orders_2 @ sk_A @ 
% 0.37/0.56             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['95', '96'])).
% 0.37/0.56  thf('98', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('99', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (r2_orders_2 @ sk_A @ 
% 0.37/0.56             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ X0)
% 0.37/0.56          | ~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | (v2_struct_0 @ sk_A))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.37/0.56  thf('100', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | ~ (m1_subset_1 @ 
% 0.37/0.56             (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56             (k2_struct_0 @ sk_A))
% 0.37/0.56        | (r2_orders_2 @ sk_A @ 
% 0.37/0.56           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['79', '99'])).
% 0.37/0.56  thf('101', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56        (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('102', plain,
% 0.37/0.56      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56        | (v2_struct_0 @ sk_A)
% 0.37/0.56        | (r2_orders_2 @ sk_A @ 
% 0.37/0.56           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56           (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)))))),
% 0.37/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.37/0.56  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('104', plain,
% 0.37/0.56      (((r2_orders_2 @ sk_A @ 
% 0.37/0.56         (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56         (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))
% 0.37/0.56        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.37/0.56      inference('clc', [status(thm)], ['102', '103'])).
% 0.37/0.56  thf('105', plain,
% 0.37/0.56      ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56        (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['75', '76'])).
% 0.37/0.56  thf('106', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['19', '24'])).
% 0.37/0.56  thf(d10_orders_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_orders_2 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.37/0.56               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.37/0.56                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf('107', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.37/0.56          | ~ (r2_orders_2 @ X13 @ X12 @ X14)
% 0.37/0.56          | ((X12) != (X14))
% 0.37/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.37/0.56          | ~ (l1_orders_2 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.37/0.56  thf('108', plain,
% 0.37/0.56      (![X13 : $i, X14 : $i]:
% 0.37/0.56         (~ (l1_orders_2 @ X13)
% 0.37/0.56          | ~ (r2_orders_2 @ X13 @ X14 @ X14)
% 0.37/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['107'])).
% 0.37/0.56  thf('109', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_orders_2 @ sk_A @ X0 @ X0)
% 0.37/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['106', '108'])).
% 0.37/0.56  thf('110', plain, ((l1_orders_2 @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('111', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X0 @ (k2_struct_0 @ sk_A))
% 0.37/0.56          | ~ (r2_orders_2 @ sk_A @ X0 @ X0))),
% 0.37/0.56      inference('demod', [status(thm)], ['109', '110'])).
% 0.37/0.56  thf('112', plain,
% 0.37/0.56      (~ (r2_orders_2 @ sk_A @ 
% 0.37/0.56          (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))) @ 
% 0.37/0.56          (sk_B @ (k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['105', '111'])).
% 0.37/0.56  thf('113', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['104', '112'])).
% 0.37/0.56  thf('114', plain,
% 0.37/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.37/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.37/0.56  thf('115', plain,
% 0.37/0.56      (![X10 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.37/0.56  thf('116', plain,
% 0.37/0.56      (![X11 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.56          | ~ (l1_struct_0 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.37/0.56  thf(t5_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.37/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.37/0.56  thf('117', plain,
% 0.37/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X6 @ X7)
% 0.37/0.56          | ~ (v1_xboole_0 @ X8)
% 0.37/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.37/0.56  thf('118', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (l1_struct_0 @ X0)
% 0.37/0.56          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['116', '117'])).
% 0.37/0.56  thf('119', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 0.37/0.56          | ~ (l1_struct_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['115', '118'])).
% 0.37/0.56  thf('120', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 0.37/0.56          | ~ (l1_struct_0 @ X0)
% 0.37/0.56          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['119'])).
% 0.37/0.56  thf('121', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_struct_0 @ X0) = (k1_xboole_0))
% 0.37/0.56          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.37/0.56          | ~ (l1_struct_0 @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['114', '120'])).
% 0.37/0.56  thf('122', plain,
% 0.37/0.56      ((~ (l1_struct_0 @ sk_A) | ((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['113', '121'])).
% 0.37/0.56  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 0.37/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('124', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['122', '123'])).
% 0.37/0.56  thf('125', plain,
% 0.37/0.56      (((k2_orders_2 @ sk_A @ k1_xboole_0) = (k2_struct_0 @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('126', plain, (((k2_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['122', '123'])).
% 0.37/0.56  thf('127', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '124', '125', '126'])).
% 0.37/0.56  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
