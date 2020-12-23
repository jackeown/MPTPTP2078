%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eNO7DQILOG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  82 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  374 ( 814 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t48_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( r2_hidden @ B @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t47_orders_2,axiom,(
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
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_orders_2 @ X25 @ X26 ) )
      | ~ ( r2_hidden @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t47_orders_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
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
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eNO7DQILOG
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 101 iterations in 0.042s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(t48_orders_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ~( r2_hidden @
% 0.20/0.49                B @ 
% 0.20/0.49                ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ~( r2_hidden @
% 0.20/0.49                   B @ 
% 0.20/0.49                   ( k1_orders_2 @
% 0.20/0.49                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t48_orders_2])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.49       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X22)
% 0.20/0.49          | ~ (m1_subset_1 @ X23 @ X22)
% 0.20/0.49          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((r2_hidden @ sk_B @ 
% 0.20/0.49        (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((r2_hidden @ sk_B @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         ((r2_hidden @ X10 @ X11)
% 0.20/0.49          | (v1_xboole_0 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X7 : $i, X9 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (r1_tarski @ (k1_tarski @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X12 : $i, X14 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf(t47_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49               ( ~( ( r2_hidden @ B @ C ) & 
% 0.20/0.49                    ( r2_hidden @ B @ ( k1_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.20/0.49          | ~ (r2_hidden @ X24 @ (k1_orders_2 @ X25 @ X26))
% 0.20/0.49          | ~ (r2_hidden @ X24 @ X26)
% 0.20/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.49          | ~ (l1_orders_2 @ X25)
% 0.20/0.49          | ~ (v5_orders_2 @ X25)
% 0.20/0.49          | ~ (v4_orders_2 @ X25)
% 0.20/0.49          | ~ (v3_orders_2 @ X25)
% 0.20/0.49          | (v2_struct_0 @ X25))),
% 0.20/0.49      inference('cnf', [status(esa)], [t47_orders_2])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49          | (v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '19'])).
% 0.20/0.49  thf('21', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (((X3) != (X2)) | (r2_hidden @ X3 @ X4) | ((X4) != (k1_tarski @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('23', plain, (![X2 : $i]: (r2_hidden @ X2 @ (k1_tarski @ X2))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.49  thf('26', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf(fc2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X18 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X18))
% 0.20/0.49          | ~ (l1_struct_0 @ X18)
% 0.20/0.49          | (v2_struct_0 @ X18))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.49  thf('29', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_orders_2, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.49  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['29', '32'])).
% 0.20/0.49  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
