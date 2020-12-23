%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xlex20L2Ys

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 (  89 expanded)
%              Number of leaves         :   31 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  448 ( 692 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t24_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ B @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( r1_orders_2 @ A @ B @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( u1_orders_2 @ X0 ) ) @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k4_tarski @ ( sk_C @ X5 ) @ ( sk_D @ X5 ) ) )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) )
      | ( ( sk_B @ ( u1_orders_2 @ X0 ) )
        = ( k4_tarski @ ( sk_C @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) @ ( sk_D @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( ( sk_B @ ( u1_orders_2 @ X0 ) )
        = ( k4_tarski @ ( sk_C @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) @ ( sk_D @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ( ( sk_B @ X7 )
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ~ ( v3_orders_2 @ X17 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X17 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_orders_2])).

thf(d1_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_relat_2 @ A @ B )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
             => ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_relat_2 @ X13 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X15 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('35',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xlex20L2Ys
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:37:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 40 iterations in 0.026s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.47  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(t24_orders_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.47            ( l1_orders_2 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( r1_orders_2 @ A @ B @ B ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t24_orders_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t2_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ X4)
% 0.21/0.47          | (v1_xboole_0 @ X4)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(d1_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X7 : $i]: ((v1_relat_1 @ X7) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.47  thf(dt_u1_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( u1_orders_2 @ A ) @ 
% 0.21/0.47         ( k1_zfmisc_1 @
% 0.21/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X22 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 0.21/0.47           (k1_zfmisc_1 @ 
% 0.21/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 0.21/0.47          | ~ (l1_orders_2 @ X22))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.47  thf(l3_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ X0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | (r2_hidden @ X1 @ 
% 0.21/0.47             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.47          | (r2_hidden @ (sk_B @ (u1_orders_2 @ X0)) @ 
% 0.21/0.47             (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_orders_2 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i]:
% 0.21/0.47         (((X5) = (k4_tarski @ (sk_C @ X5) @ (sk_D @ X5)))
% 0.21/0.47          | ~ (r2_hidden @ X5 @ X6)
% 0.21/0.47          | ~ (v1_relat_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ 
% 0.21/0.47               (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ((sk_B @ (u1_orders_2 @ X0))
% 0.21/0.47              = (k4_tarski @ (sk_C @ (sk_B @ (u1_orders_2 @ X0))) @ 
% 0.21/0.47                 (sk_D @ (sk_B @ (u1_orders_2 @ X0))))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf(fc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.47          | ((sk_B @ (u1_orders_2 @ X0))
% 0.21/0.47              = (k4_tarski @ (sk_C @ (sk_B @ (u1_orders_2 @ X0))) @ 
% 0.21/0.47                 (sk_D @ (sk_B @ (u1_orders_2 @ X0))))))),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.47         ((v1_relat_1 @ X7) | ((sk_B @ X7) != (k4_tarski @ X8 @ X9)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X0 : $i]: ((v1_relat_1 @ (u1_orders_2 @ X0)) | ~ (l1_orders_2 @ X0))),
% 0.21/0.47      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf(d4_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ( v3_orders_2 @ A ) <=>
% 0.21/0.47         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X17 : $i]:
% 0.21/0.47         (~ (v3_orders_2 @ X17)
% 0.21/0.47          | (r1_relat_2 @ (u1_orders_2 @ X17) @ (u1_struct_0 @ X17))
% 0.21/0.47          | ~ (l1_orders_2 @ X17))),
% 0.21/0.47      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.21/0.47  thf(d1_relat_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( r1_relat_2 @ A @ B ) <=>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( r2_hidden @ C @ B ) =>
% 0.21/0.47               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.47         (~ (r1_relat_2 @ X13 @ X14)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X15 @ X15) @ X13)
% 0.21/0.47          | ~ (r2_hidden @ X15 @ X14)
% 0.21/0.47          | ~ (v1_relat_1 @ X13))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | ~ (v3_orders_2 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (l1_orders_2 @ X0)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (v3_orders_2 @ X0)
% 0.21/0.47          | ~ (l1_orders_2 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v3_orders_2 @ X0)
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.21/0.47          | ~ (l1_orders_2 @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.21/0.47        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '19'])).
% 0.21/0.47  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.47  thf(d9_orders_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_orders_2 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.47                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.47          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (u1_orders_2 @ X19))
% 0.21/0.47          | (r1_orders_2 @ X19 @ X18 @ X20)
% 0.21/0.47          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.47          | ~ (l1_orders_2 @ X19))),
% 0.21/0.47      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.47        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)
% 0.21/0.47        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf(fc2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X16 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.21/0.47          | ~ (l1_struct_0 @ X16)
% 0.21/0.47          | (v2_struct_0 @ X16))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.47  thf('33', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_l1_orders_2, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.47  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.47  thf('37', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '36'])).
% 0.21/0.47  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
