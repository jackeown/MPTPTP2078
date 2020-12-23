%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upGpnG47ZG

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:25 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   59 (  68 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  344 ( 410 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ( m1_subset_1 @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( m1_subset_1 @ X31 @ X32 )
      | ~ ( r2_hidden @ X31 @ X32 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( m1_subset_1 @ ( k1_tarski @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['9','10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( r2_hidden @ X5 @ X8 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X11 @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r2_hidden @ X9 @ X7 )
      | ( X8
       != ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['2','11','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.upGpnG47ZG
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:27:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 202 iterations in 0.103s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(t63_subset_1, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.58       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ( r2_hidden @ A @ B ) =>
% 0.39/0.58          ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t63_subset_1])).
% 0.39/0.58  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d1_xboole_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('2', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('3', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d2_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_xboole_0 @ A ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.39/0.58       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X31 : $i, X32 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X31 @ X32)
% 0.39/0.58          | (m1_subset_1 @ X31 @ X32)
% 0.39/0.58          | (v1_xboole_0 @ X32))),
% 0.39/0.58      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X31 : $i, X32 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X31 @ X32) | ~ (r2_hidden @ X31 @ X32))),
% 0.39/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.58  thf('7', plain, ((m1_subset_1 @ sk_A @ sk_B_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '6'])).
% 0.39/0.58  thf(t55_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ A ) =>
% 0.39/0.58       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.39/0.58         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X34 : $i, X35 : $i]:
% 0.39/0.58         (((X34) = (k1_xboole_0))
% 0.39/0.58          | ~ (m1_subset_1 @ X35 @ X34)
% 0.39/0.58          | (m1_subset_1 @ (k1_tarski @ X35) @ (k1_zfmisc_1 @ X34)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_subset_1])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (((m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))
% 0.39/0.58        | ((sk_B_1) = (k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (~ (m1_subset_1 @ (k1_tarski @ sk_A) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('11', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.39/0.58      inference('clc', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.58  thf('12', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.58  thf(t83_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i]:
% 0.39/0.58         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.39/0.58      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.58  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf(d4_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.39/0.58       ( ![D:$i]:
% 0.39/0.58         ( ( r2_hidden @ D @ C ) <=>
% 0.39/0.58           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X5 @ X6)
% 0.39/0.58          | ~ (r2_hidden @ X5 @ X7)
% 0.39/0.58          | (r2_hidden @ X5 @ X8)
% 0.39/0.58          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         ((r2_hidden @ X5 @ (k3_xboole_0 @ X6 @ X7))
% 0.39/0.58          | ~ (r2_hidden @ X5 @ X7)
% 0.39/0.58          | ~ (r2_hidden @ X5 @ X6))),
% 0.39/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.39/0.58          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X0)
% 0.39/0.58          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['15', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.39/0.58          | (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.58  thf(t100_xboole_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X15 : $i, X16 : $i]:
% 0.39/0.58         ((k4_xboole_0 @ X15 @ X16)
% 0.39/0.58           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.58  thf(t1_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.39/0.58       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X11 @ X12)
% 0.39/0.58          | ~ (r2_hidden @ X11 @ X13)
% 0.39/0.58          | ~ (r2_hidden @ X11 @ (k5_xboole_0 @ X12 @ X13)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ X2 @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X9 @ X8)
% 0.39/0.58          | (r2_hidden @ X9 @ X7)
% 0.39/0.58          | ((X8) != (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.39/0.58         ((r2_hidden @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['25', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.58          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.39/0.58      inference('clc', [status(thm)], ['24', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((~ (r2_hidden @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 0.39/0.58        | (v1_xboole_0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.58  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('clc', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain, ($false),
% 0.39/0.58      inference('demod', [status(thm)], ['2', '11', '33'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
