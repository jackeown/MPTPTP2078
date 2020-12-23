%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZBF4ziEBR

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:33 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  433 ( 667 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

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
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
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

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k4_tarski @ ( sk_E @ X12 @ X13 @ X14 ) @ ( sk_F @ X12 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_orders_2 @ X0 ) )
      | ( X1
        = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ( ( sk_B @ ( u1_orders_2 @ X0 ) )
        = ( k4_tarski @ ( sk_E @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) @ ( sk_F @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_orders_2 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ( ( sk_B @ X5 )
       != ( k4_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_relat_1 @ ( u1_orders_2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d4_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v3_orders_2 @ A )
      <=> ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
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

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_relat_2 @ X9 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X11 ) @ X9 )
      | ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v1_relat_1 @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X1 ) @ ( u1_orders_2 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B_1 @ sk_B_1 ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( u1_orders_2 @ X19 ) )
      | ( r1_orders_2 @ X19 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ZBF4ziEBR
% 0.14/0.37  % Computer   : n016.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:03:49 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 69 iterations in 0.052s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.23/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.53  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.23/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.23/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.23/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.23/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.53  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(t24_orders_2, conjecture,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.53           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i]:
% 0.23/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.23/0.53            ( l1_orders_2 @ A ) ) =>
% 0.23/0.53          ( ![B:$i]:
% 0.23/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.53              ( r1_orders_2 @ A @ B @ B ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t24_orders_2])).
% 0.23/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(d2_subset_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (m1_subset_1 @ X0 @ X1)
% 0.23/0.53          | (r2_hidden @ X0 @ X1)
% 0.23/0.53          | (v1_xboole_0 @ X1))),
% 0.23/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.53        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf(d1_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) <=>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ~( ( r2_hidden @ B @ A ) & 
% 0.23/0.53              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (![X5 : $i]: ((v1_relat_1 @ X5) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.23/0.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.23/0.53  thf(dt_u1_orders_2, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( l1_orders_2 @ A ) =>
% 0.23/0.53       ( m1_subset_1 @
% 0.23/0.54         ( u1_orders_2 @ A ) @ 
% 0.23/0.54         ( k1_zfmisc_1 @
% 0.23/0.54           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X22 : $i]:
% 0.23/0.54         ((m1_subset_1 @ (u1_orders_2 @ X22) @ 
% 0.23/0.54           (k1_zfmisc_1 @ 
% 0.23/0.54            (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X22))))
% 0.23/0.54          | ~ (l1_orders_2 @ X22))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.23/0.54  thf(t6_relset_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.23/0.54       ( ~( ( r2_hidden @ A @ D ) & 
% 0.23/0.54            ( ![E:$i,F:$i]:
% 0.23/0.54              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.23/0.54                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.54         (((X14)
% 0.23/0.54            = (k4_tarski @ (sk_E @ X12 @ X13 @ X14) @ (sk_F @ X12 @ X13 @ X14)))
% 0.23/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12)))
% 0.23/0.54          | ~ (r2_hidden @ X14 @ X15))),
% 0.23/0.54      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 0.23/0.54          | ((X1)
% 0.23/0.54              = (k4_tarski @ 
% 0.23/0.54                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 0.23/0.54                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1))))),
% 0.23/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((v1_relat_1 @ (u1_orders_2 @ X0))
% 0.23/0.54          | ((sk_B @ (u1_orders_2 @ X0))
% 0.23/0.54              = (k4_tarski @ 
% 0.23/0.54                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.23/0.54                  (sk_B @ (u1_orders_2 @ X0))) @ 
% 0.23/0.54                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.23/0.54                  (sk_B @ (u1_orders_2 @ X0)))))
% 0.23/0.54          | ~ (l1_orders_2 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.54         ((v1_relat_1 @ X5) | ((sk_B @ X5) != (k4_tarski @ X6 @ X7)))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.23/0.54      inference('clc', [status(thm)], ['8', '9'])).
% 0.23/0.54  thf(d4_orders_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ( v3_orders_2 @ A ) <=>
% 0.23/0.54         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X17 : $i]:
% 0.23/0.54         (~ (v3_orders_2 @ X17)
% 0.23/0.54          | (r1_relat_2 @ (u1_orders_2 @ X17) @ (u1_struct_0 @ X17))
% 0.23/0.54          | ~ (l1_orders_2 @ X17))),
% 0.23/0.54      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.23/0.54  thf(d1_relat_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( v1_relat_1 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( r1_relat_2 @ A @ B ) <=>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( r2_hidden @ C @ B ) =>
% 0.23/0.54               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.54         (~ (r1_relat_2 @ X9 @ X10)
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ X11 @ X11) @ X9)
% 0.23/0.54          | ~ (r2_hidden @ X11 @ X10)
% 0.23/0.54          | ~ (v1_relat_1 @ X9))),
% 0.23/0.54      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ X0)
% 0.23/0.54          | ~ (v3_orders_2 @ X0)
% 0.23/0.54          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.23/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (l1_orders_2 @ X0)
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.23/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.23/0.54          | ~ (v3_orders_2 @ X0)
% 0.23/0.54          | ~ (l1_orders_2 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (v3_orders_2 @ X0)
% 0.23/0.54          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.23/0.54          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.23/0.54          | ~ (l1_orders_2 @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.23/0.54        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.23/0.54        | ~ (v3_orders_2 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['3', '15'])).
% 0.23/0.54  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.23/0.54      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.23/0.54  thf(d9_orders_2, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( l1_orders_2 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54           ( ![C:$i]:
% 0.23/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.54               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.23/0.54                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.23/0.54          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (u1_orders_2 @ X19))
% 0.23/0.54          | (r1_orders_2 @ X19 @ X18 @ X20)
% 0.23/0.54          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.23/0.54          | ~ (l1_orders_2 @ X19))),
% 0.23/0.54      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.23/0.54  thf('21', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | ~ (l1_orders_2 @ sk_A)
% 0.23/0.54        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)
% 0.23/0.54        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('23', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.54        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.23/0.54      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.23/0.54  thf('26', plain, (~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('27', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.23/0.54      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf(fc2_struct_0, axiom,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.54  thf('28', plain,
% 0.23/0.54      (![X16 : $i]:
% 0.23/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.23/0.54          | ~ (l1_struct_0 @ X16)
% 0.23/0.54          | (v2_struct_0 @ X16))),
% 0.23/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.54  thf('29', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.54  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf(dt_l1_orders_2, axiom,
% 0.23/0.54    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.54  thf('31', plain,
% 0.23/0.54      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 0.23/0.54      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.23/0.54  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.54  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['29', '32'])).
% 0.23/0.54  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
