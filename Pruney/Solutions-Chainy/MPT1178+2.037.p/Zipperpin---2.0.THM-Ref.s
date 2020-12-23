%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dKfozkxG2n

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 128 expanded)
%              Number of leaves         :   25 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  466 (1553 expanded)
%              Number of equality atoms :   15 (  63 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

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
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_orders_1 @ X10 @ ( k1_orders_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m2_orders_2 @ ( sk_C @ X10 @ X9 ) @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[existence_m2_orders_2])).

thf('2',plain,
    ( ( m2_orders_2 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 )
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
    ( ( m2_orders_2 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m2_orders_2 @ ( sk_C @ sk_B_2 @ sk_A ) @ sk_A @ sk_B_2 ),
    inference(clc,[status(thm)],['7','8'])).

thf('11',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_orders_1 @ X3 @ ( k1_orders_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( X5
       != ( k4_orders_2 @ X4 @ X3 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( m2_orders_2 @ X6 @ X4 @ X3 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m2_orders_2 @ X6 @ X4 @ X3 )
      | ( r2_hidden @ X6 @ ( k4_orders_2 @ X4 @ X3 ) )
      | ~ ( m1_orders_1 @ X3 @ ( k1_orders_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C @ sk_B_2 @ sk_A ) @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k3_tarski @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_C @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(demod,[status(thm)],['9','27'])).

thf('29',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_orders_1 @ X11 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ ( u1_struct_0 @ X12 ) ) @ X13 )
      | ~ ( m2_orders_2 @ X13 @ X12 @ X11 )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
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
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['28','38'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dKfozkxG2n
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 111 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.49  thf(t87_orders_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(existence_m2_orders_2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.20/0.49         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.49       ( ?[C:$i]: ( m2_orders_2 @ C @ A @ B ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (~ (l1_orders_2 @ X9)
% 0.20/0.49          | ~ (v5_orders_2 @ X9)
% 0.20/0.49          | ~ (v4_orders_2 @ X9)
% 0.20/0.49          | ~ (v3_orders_2 @ X9)
% 0.20/0.49          | (v2_struct_0 @ X9)
% 0.20/0.49          | ~ (m1_orders_1 @ X10 @ (k1_orders_1 @ (u1_struct_0 @ X9)))
% 0.20/0.49          | (m2_orders_2 @ (sk_C @ X10 @ X9) @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [existence_m2_orders_2])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (((m2_orders_2 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A @ sk_B_2)
% 0.20/0.49        | (v2_struct_0 @ sk_A)
% 0.20/0.49        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((m2_orders_2 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A @ sk_B_2)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.20/0.49  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((m2_orders_2 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A @ sk_B_2)),
% 0.20/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain, ((m2_orders_2 @ (sk_C @ sk_B_2 @ sk_A) @ sk_A @ sk_B_2)),
% 0.20/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d17_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (m1_orders_1 @ X3 @ (k1_orders_1 @ (u1_struct_0 @ X4)))
% 0.20/0.49          | ((X5) != (k4_orders_2 @ X4 @ X3))
% 0.20/0.49          | (r2_hidden @ X6 @ X5)
% 0.20/0.49          | ~ (m2_orders_2 @ X6 @ X4 @ X3)
% 0.20/0.49          | ~ (l1_orders_2 @ X4)
% 0.20/0.49          | ~ (v5_orders_2 @ X4)
% 0.20/0.49          | ~ (v4_orders_2 @ X4)
% 0.20/0.49          | ~ (v3_orders_2 @ X4)
% 0.20/0.49          | (v2_struct_0 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X4)
% 0.20/0.49          | ~ (v3_orders_2 @ X4)
% 0.20/0.49          | ~ (v4_orders_2 @ X4)
% 0.20/0.49          | ~ (v5_orders_2 @ X4)
% 0.20/0.49          | ~ (l1_orders_2 @ X4)
% 0.20/0.49          | ~ (m2_orders_2 @ X6 @ X4 @ X3)
% 0.20/0.49          | (r2_hidden @ X6 @ (k4_orders_2 @ X4 @ X3))
% 0.20/0.49          | ~ (m1_orders_1 @ X3 @ (k1_orders_1 @ (u1_struct_0 @ X4))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.49  thf('15', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.20/0.49          | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.20/0.49  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.20/0.49          | (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((r2_hidden @ (sk_C @ sk_B_2 @ sk_A) @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t91_orders_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( ![B:$i]:
% 0.20/0.49              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.20/0.49       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (((X14) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X14 @ X15)
% 0.20/0.49          | ((k3_tarski @ X15) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.49  thf('27', plain, (((sk_C @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '26'])).
% 0.20/0.49  thf('28', plain, ((m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t79_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.20/0.49               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (m1_orders_1 @ X11 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ X11 @ (u1_struct_0 @ X12)) @ X13)
% 0.20/0.49          | ~ (m2_orders_2 @ X13 @ X12 @ X11)
% 0.20/0.49          | ~ (l1_orders_2 @ X12)
% 0.20/0.49          | ~ (v5_orders_2 @ X12)
% 0.20/0.49          | ~ (v4_orders_2 @ X12)
% 0.20/0.49          | ~ (v3_orders_2 @ X12)
% 0.20/0.49          | (v2_struct_0 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t79_orders_2])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49          | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('33', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v2_struct_0 @ sk_A)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.20/0.49          | (r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.20/0.49  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ X0)
% 0.20/0.49          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.20/0.49      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((r2_hidden @ (k1_funct_1 @ sk_B_2 @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '38'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('41', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('43', plain, ($false), inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
