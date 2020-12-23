%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYze7cUL4k

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  464 (1551 expanded)
%              Number of equality atoms :    5 (  53 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ? [C: $i] :
          ( m2_orders_2 @ C @ A @ B ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X13 @ X12 ) @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ ( u1_struct_0 @ X15 ) ) @ X16 )
      | ~ ( m2_orders_2 @ X16 @ X15 @ X14 )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ~ ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m2_orders_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['7','8'])).

thf('24',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k4_orders_2 @ X7 @ X6 ) )
      | ( r2_hidden @ X9 @ X8 )
      | ~ ( m2_orders_2 @ X9 @ X7 @ X6 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( m2_orders_2 @ X9 @ X7 @ X6 )
      | ( r2_hidden @ X9 @ ( k4_orders_2 @ X7 @ X6 ) )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('37',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_orders_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_C @ sk_B @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['22','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYze7cUL4k
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:48:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 20 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.48  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(t87_orders_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(existence_m2_orders_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.48         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (l1_orders_2 @ X12)
% 0.21/0.48          | ~ (v5_orders_2 @ X12)
% 0.21/0.48          | ~ (v4_orders_2 @ X12)
% 0.21/0.48          | ~ (v3_orders_2 @ X12)
% 0.21/0.48          | (v2_struct_0 @ X12)
% 0.21/0.48          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.21/0.48          | (m2_orders_2 @ (sk_C @ X13 @ X12) @ X12 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.21/0.48        | (v2_struct_0 @ sk_A)
% 0.21/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.21/0.48        | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.48  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t79_orders_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.48               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ X14 @ (u1_struct_0 @ X15)) @ X16)
% 0.21/0.48          | ~ (m2_orders_2 @ X16 @ X15 @ X14)
% 0.21/0.48          | ~ (l1_orders_2 @ X15)
% 0.21/0.48          | ~ (v5_orders_2 @ X15)
% 0.21/0.48          | ~ (v4_orders_2 @ X15)
% 0.21/0.48          | ~ (v3_orders_2 @ X15)
% 0.21/0.48          | (v2_struct_0 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v2_struct_0 @ sk_A)
% 0.21/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.48          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.21/0.48  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 0.21/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 0.21/0.48      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.21/0.48        (sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '19'])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]: (~ (r2_hidden @ X4 @ X5) | ~ (r1_tarski @ X5 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (~ (r1_tarski @ (sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48          (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((m2_orders_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d17_orders_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.48               ( ![D:$i]:
% 0.21/0.48                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.48         (~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7)))
% 0.21/0.48          | ((X8) != (k4_orders_2 @ X7 @ X6))
% 0.21/0.48          | (r2_hidden @ X9 @ X8)
% 0.21/0.48          | ~ (m2_orders_2 @ X9 @ X7 @ X6)
% 0.21/0.48          | ~ (l1_orders_2 @ X7)
% 0.21/0.48          | ~ (v5_orders_2 @ X7)
% 0.21/0.48          | ~ (v4_orders_2 @ X7)
% 0.21/0.48          | ~ (v3_orders_2 @ X7)
% 0.21/0.48          | (v2_struct_0 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.21/0.48         ((v2_struct_0 @ X7)
% 0.21/0.48          | ~ (v3_orders_2 @ X7)
% 0.21/0.48          | ~ (v4_orders_2 @ X7)
% 0.21/0.48          | ~ (v5_orders_2 @ X7)
% 0.21/0.48          | ~ (l1_orders_2 @ X7)
% 0.21/0.48          | ~ (m2_orders_2 @ X9 @ X7 @ X6)
% 0.21/0.48          | (r2_hidden @ X9 @ (k4_orders_2 @ X7 @ X6))
% 0.21/0.48          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.21/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.48          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.48          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.48  thf('28', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B))
% 0.21/0.48          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.48          | (v2_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.21/0.48  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 0.21/0.48          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('clc', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t56_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.48       ( r1_tarski @ C @ B ) ))).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r1_tarski @ (k3_tarski @ X1) @ X2)
% 0.21/0.48          | ~ (r2_hidden @ X3 @ X1)
% 0.21/0.48          | (r1_tarski @ X3 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.48          | (r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_tarski @ X1 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X1 @ (k4_orders_2 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain, (![X0 : $i]: (r1_tarski @ (sk_C @ sk_B @ sk_A) @ X0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '40'])).
% 0.21/0.48  thf('42', plain, ($false), inference('demod', [status(thm)], ['22', '41'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
