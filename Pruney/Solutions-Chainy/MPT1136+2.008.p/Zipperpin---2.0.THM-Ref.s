%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64J7CRqTOj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  83 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  426 ( 660 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_relat_2_type,type,(
    r1_relat_2: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
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
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ~ ( l1_orders_2 @ X23 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k4_tarski @ ( sk_E @ X13 @ X14 @ X15 ) @ ( sk_F @ X13 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X13 ) ) )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ( ( sk_B @ X6 )
       != ( k4_tarski @ X7 @ X8 ) ) ) ),
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
    ! [X18: $i] :
      ( ~ ( v3_orders_2 @ X18 )
      | ( r1_relat_2 @ ( u1_orders_2 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_relat_2 @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X12 ) @ X10 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ ( u1_orders_2 @ X20 ) )
      | ( r1_orders_2 @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
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
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
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
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64J7CRqTOj
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 81 iterations in 0.057s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.51  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(r1_relat_2_type, type, r1_relat_2: $i > $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(t24_orders_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( r1_orders_2 @ A @ B @ B ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.51            ( l1_orders_2 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51              ( r1_orders_2 @ A @ B @ B ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t24_orders_2])).
% 0.21/0.51  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         ((r2_hidden @ X2 @ X3)
% 0.21/0.51          | (v1_xboole_0 @ X3)
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf(d1_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.51              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X6 : $i]: ((v1_relat_1 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.51  thf(dt_u1_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( u1_orders_2 @ A ) @ 
% 0.21/0.51         ( k1_zfmisc_1 @
% 0.21/0.51           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X23 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (u1_orders_2 @ X23) @ 
% 0.21/0.51           (k1_zfmisc_1 @ 
% 0.21/0.51            (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X23))))
% 0.21/0.51          | ~ (l1_orders_2 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.51  thf(t6_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.21/0.51       ( ~( ( r2_hidden @ A @ D ) & 
% 0.21/0.51            ( ![E:$i,F:$i]:
% 0.21/0.51              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.51                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         (((X15)
% 0.21/0.51            = (k4_tarski @ (sk_E @ X13 @ X14 @ X15) @ (sk_F @ X13 @ X14 @ X15)))
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X13)))
% 0.21/0.51          | ~ (r2_hidden @ X15 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t6_relset_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ (u1_orders_2 @ X0))
% 0.21/0.51          | ((X1)
% 0.21/0.51              = (k4_tarski @ 
% 0.21/0.51                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1) @ 
% 0.21/0.51                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X1))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.51          | ((sk_B @ (u1_orders_2 @ X0))
% 0.21/0.51              = (k4_tarski @ 
% 0.21/0.51                 (sk_E @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.21/0.51                  (sk_B @ (u1_orders_2 @ X0))) @ 
% 0.21/0.51                 (sk_F @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.21/0.51                  (sk_B @ (u1_orders_2 @ X0)))))
% 0.21/0.51          | ~ (l1_orders_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X6) | ((sk_B @ X6) != (k4_tarski @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i]: (~ (l1_orders_2 @ X0) | (v1_relat_1 @ (u1_orders_2 @ X0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['8', '9'])).
% 0.21/0.51  thf(d4_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ( v3_orders_2 @ A ) <=>
% 0.21/0.51         ( r1_relat_2 @ ( u1_orders_2 @ A ) @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X18 : $i]:
% 0.21/0.51         (~ (v3_orders_2 @ X18)
% 0.21/0.51          | (r1_relat_2 @ (u1_orders_2 @ X18) @ (u1_struct_0 @ X18))
% 0.21/0.51          | ~ (l1_orders_2 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_orders_2])).
% 0.21/0.51  thf(d1_relat_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( r1_relat_2 @ A @ B ) <=>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r2_hidden @ C @ B ) =>
% 0.21/0.51               ( r2_hidden @ ( k4_tarski @ C @ C ) @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.51         (~ (r1_relat_2 @ X10 @ X11)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X12 @ X12) @ X10)
% 0.21/0.51          | ~ (r2_hidden @ X12 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X10))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_relat_2])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X0)
% 0.21/0.51          | ~ (v3_orders_2 @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ (u1_orders_2 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_orders_2 @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v3_orders_2 @ X0)
% 0.21/0.51          | ~ (l1_orders_2 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v3_orders_2 @ X0)
% 0.21/0.51          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X1 @ X1) @ (u1_orders_2 @ X0))
% 0.21/0.51          | ~ (l1_orders_2 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A))
% 0.21/0.51        | ~ (v3_orders_2 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.51  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r2_hidden @ (k4_tarski @ sk_B_1 @ sk_B_1) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.51  thf(d9_orders_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_orders_2 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.51               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.51                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ (u1_orders_2 @ X20))
% 0.21/0.51          | (r1_orders_2 @ X20 @ X19 @ X21)
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.21/0.51          | ~ (l1_orders_2 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.51        | (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.21/0.51      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.21/0.51  thf('26', plain, (~ (r1_orders_2 @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf(fc2_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X17 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.51          | ~ (l1_struct_0 @ X17)
% 0.21/0.51          | (v2_struct_0 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.51  thf('29', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_orders_2, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_orders_2 @ X22))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.51  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '32'])).
% 0.21/0.51  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
