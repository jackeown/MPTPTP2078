%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDERAsEKlr

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  289 ( 376 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ( m1_subset_1 @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ~ ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('12',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X21 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_2 @ X0 )
        = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_B_1 @ ( k3_xboole_0 @ sk_B_2 @ X0 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('20',plain,(
    r2_hidden @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r1_tarski @ X15 @ X13 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('22',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_tarski @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    k1_xboole_0 = sk_B_2 ),
    inference('sup+',[status(thm)],['15','25'])).

thf('27',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NDERAsEKlr
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 154 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t7_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf(d4_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.51          | (r2_hidden @ X7 @ X5)
% 0.21/0.51          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.51         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_B_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.51  thf(d2_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X17 @ X18)
% 0.21/0.51          | (m1_subset_1 @ X17 @ X18)
% 0.21/0.51          | (v1_xboole_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.21/0.51      inference('clc', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | (m1_subset_1 @ (sk_B_1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X9) @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X7 @ X6)
% 0.21/0.51          | (r2_hidden @ X7 @ X4)
% 0.21/0.51          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.51         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ (sk_B_1 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.51  thf(t10_subset_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51            ( ![C:$i]:
% 0.21/0.51              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.51               ( ![C:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t10_subset_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X21 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X21 @ sk_B_2) | ~ (m1_subset_1 @ X21 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ sk_B_2 @ X0) = (k1_xboole_0))
% 0.21/0.51          | ~ (m1_subset_1 @ (sk_B_1 @ (k3_xboole_0 @ sk_B_2 @ X0)) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      ((((k3_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((k3_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.51  thf('15', plain, (((k3_xboole_0 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ X18)
% 0.21/0.51          | (r2_hidden @ X17 @ X18)
% 0.21/0.51          | (v1_xboole_0 @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.51        | (r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf(fc1_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('19', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.51  thf('20', plain, ((r2_hidden @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf(d1_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.51          | (r1_tarski @ X15 @ X13)
% 0.21/0.51          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X13 : $i, X15 : $i]:
% 0.21/0.51         ((r1_tarski @ X15 @ X13) | ~ (r2_hidden @ X15 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.51  thf('23', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.51  thf(t28_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.51  thf('25', plain, (((k3_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, (((k1_xboole_0) = (sk_B_2))),
% 0.21/0.51      inference('sup+', [status(thm)], ['15', '25'])).
% 0.21/0.51  thf('27', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('28', plain, ($false),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
