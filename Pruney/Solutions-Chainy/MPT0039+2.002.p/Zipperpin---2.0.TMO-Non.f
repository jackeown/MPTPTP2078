%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RtjFRTIjhF

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:58 EST 2020

% Result     : Timeout 59.52s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of leaves         :   10 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  424 ( 917 expanded)
%              Number of equality atoms :   39 (  80 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(t32_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ B )
          = ( k4_xboole_0 @ B @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_A @ sk_A @ X0 ) @ sk_B )
      | ( sk_A
        = ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_A )
      | ( sk_B
        = ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','10'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ X0 @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('30',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_B = sk_A ),
    inference('sup+',[status(thm)],['23','31'])).

thf('33',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RtjFRTIjhF
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:08:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 59.52/59.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 59.52/59.73  % Solved by: fo/fo7.sh
% 59.52/59.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.52/59.73  % done 24636 iterations in 59.269s
% 59.52/59.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 59.52/59.73  % SZS output start Refutation
% 59.52/59.73  thf(sk_B_type, type, sk_B: $i).
% 59.52/59.73  thf(sk_A_type, type, sk_A: $i).
% 59.52/59.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 59.52/59.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 59.52/59.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 59.52/59.73  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 59.52/59.73  thf(d4_xboole_0, axiom,
% 59.52/59.73    (![A:$i,B:$i,C:$i]:
% 59.52/59.73     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 59.52/59.73       ( ![D:$i]:
% 59.52/59.73         ( ( r2_hidden @ D @ C ) <=>
% 59.52/59.73           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 59.52/59.73  thf('0', plain,
% 59.52/59.73      (![X3 : $i, X4 : $i, X7 : $i]:
% 59.52/59.73         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 59.52/59.73          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 59.52/59.73          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 59.52/59.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 59.52/59.73  thf('1', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 59.52/59.73          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 59.52/59.73      inference('eq_fact', [status(thm)], ['0'])).
% 59.52/59.73  thf(d5_xboole_0, axiom,
% 59.52/59.73    (![A:$i,B:$i,C:$i]:
% 59.52/59.73     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 59.52/59.73       ( ![D:$i]:
% 59.52/59.73         ( ( r2_hidden @ D @ C ) <=>
% 59.52/59.73           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 59.52/59.73  thf('2', plain,
% 59.52/59.73      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 59.52/59.73         (~ (r2_hidden @ X8 @ X9)
% 59.52/59.73          | (r2_hidden @ X8 @ X10)
% 59.52/59.73          | (r2_hidden @ X8 @ X11)
% 59.52/59.73          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 59.52/59.73      inference('cnf', [status(esa)], [d5_xboole_0])).
% 59.52/59.73  thf('3', plain,
% 59.52/59.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 59.52/59.73         ((r2_hidden @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 59.52/59.73          | (r2_hidden @ X8 @ X10)
% 59.52/59.73          | ~ (r2_hidden @ X8 @ X9))),
% 59.52/59.73      inference('simplify', [status(thm)], ['2'])).
% 59.52/59.73  thf('4', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.52/59.73         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 59.52/59.73          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X2)
% 59.52/59.73          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['1', '3'])).
% 59.52/59.73  thf(t32_xboole_1, conjecture,
% 59.52/59.73    (![A:$i,B:$i]:
% 59.52/59.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 59.52/59.73       ( ( A ) = ( B ) ) ))).
% 59.52/59.73  thf(zf_stmt_0, negated_conjecture,
% 59.52/59.73    (~( ![A:$i,B:$i]:
% 59.52/59.73        ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 59.52/59.73          ( ( A ) = ( B ) ) ) )),
% 59.52/59.73    inference('cnf.neg', [status(esa)], [t32_xboole_1])).
% 59.52/59.73  thf('5', plain,
% 59.52/59.73      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 59.52/59.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.52/59.73  thf('6', plain,
% 59.52/59.73      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 59.52/59.73         (~ (r2_hidden @ X12 @ X11)
% 59.52/59.73          | (r2_hidden @ X12 @ X9)
% 59.52/59.73          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 59.52/59.73      inference('cnf', [status(esa)], [d5_xboole_0])).
% 59.52/59.73  thf('7', plain,
% 59.52/59.73      (![X9 : $i, X10 : $i, X12 : $i]:
% 59.52/59.73         ((r2_hidden @ X12 @ X9)
% 59.52/59.73          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 59.52/59.73      inference('simplify', [status(thm)], ['6'])).
% 59.52/59.73  thf('8', plain,
% 59.52/59.73      (![X0 : $i]:
% 59.52/59.73         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))
% 59.52/59.73          | (r2_hidden @ X0 @ sk_B))),
% 59.52/59.73      inference('sup-', [status(thm)], ['5', '7'])).
% 59.52/59.73  thf('9', plain,
% 59.52/59.73      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 59.52/59.73         (~ (r2_hidden @ X12 @ X11)
% 59.52/59.73          | ~ (r2_hidden @ X12 @ X10)
% 59.52/59.73          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 59.52/59.73      inference('cnf', [status(esa)], [d5_xboole_0])).
% 59.52/59.73  thf('10', plain,
% 59.52/59.73      (![X9 : $i, X10 : $i, X12 : $i]:
% 59.52/59.73         (~ (r2_hidden @ X12 @ X10)
% 59.52/59.73          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 59.52/59.73      inference('simplify', [status(thm)], ['9'])).
% 59.52/59.73  thf('11', plain,
% 59.52/59.73      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 59.52/59.73      inference('clc', [status(thm)], ['8', '10'])).
% 59.52/59.73  thf('12', plain,
% 59.52/59.73      (![X0 : $i]:
% 59.52/59.73         ((r2_hidden @ (sk_D @ sk_A @ sk_A @ X0) @ sk_B)
% 59.52/59.73          | ((sk_A) = (k3_xboole_0 @ X0 @ sk_A)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['4', '11'])).
% 59.52/59.73  thf('13', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 59.52/59.73          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 59.52/59.73      inference('eq_fact', [status(thm)], ['0'])).
% 59.52/59.73  thf('14', plain,
% 59.52/59.73      (![X3 : $i, X4 : $i, X7 : $i]:
% 59.52/59.73         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 59.52/59.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 59.52/59.73  thf('15', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 59.52/59.73          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['13', '14'])).
% 59.52/59.73  thf('16', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 59.52/59.73          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 59.52/59.73      inference('simplify', [status(thm)], ['15'])).
% 59.52/59.73  thf('17', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 59.52/59.73          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 59.52/59.73      inference('eq_fact', [status(thm)], ['0'])).
% 59.52/59.73  thf('18', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 59.52/59.73      inference('clc', [status(thm)], ['16', '17'])).
% 59.52/59.73  thf('19', plain,
% 59.52/59.73      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 59.52/59.73        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['12', '18'])).
% 59.52/59.73  thf(commutativity_k3_xboole_0, axiom,
% 59.52/59.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 59.52/59.73  thf('20', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.52/59.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.52/59.73  thf('21', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 59.52/59.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 59.52/59.73  thf('22', plain,
% 59.52/59.73      ((((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))
% 59.52/59.73        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 59.52/59.73      inference('demod', [status(thm)], ['19', '20', '21'])).
% 59.52/59.73  thf('23', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 59.52/59.73      inference('simplify', [status(thm)], ['22'])).
% 59.52/59.73  thf('24', plain,
% 59.52/59.73      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_B @ sk_A))),
% 59.52/59.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.52/59.73  thf('25', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.52/59.73         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 59.52/59.73          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X2)
% 59.52/59.73          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['1', '3'])).
% 59.52/59.73  thf('26', plain,
% 59.52/59.73      (![X0 : $i]:
% 59.52/59.73         ((r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ sk_B))
% 59.52/59.73          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ sk_A)
% 59.52/59.73          | ((sk_B) = (k3_xboole_0 @ X0 @ sk_B)))),
% 59.52/59.73      inference('sup+', [status(thm)], ['24', '25'])).
% 59.52/59.73  thf('27', plain,
% 59.52/59.73      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 59.52/59.73      inference('clc', [status(thm)], ['8', '10'])).
% 59.52/59.73  thf('28', plain,
% 59.52/59.73      (![X0 : $i]:
% 59.52/59.73         (((sk_B) = (k3_xboole_0 @ X0 @ sk_B))
% 59.52/59.73          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ sk_A))),
% 59.52/59.73      inference('clc', [status(thm)], ['26', '27'])).
% 59.52/59.73  thf('29', plain,
% 59.52/59.73      (![X0 : $i, X1 : $i]:
% 59.52/59.73         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 59.52/59.73          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 59.52/59.73      inference('clc', [status(thm)], ['16', '17'])).
% 59.52/59.73  thf('30', plain,
% 59.52/59.73      ((((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))
% 59.52/59.73        | ((sk_B) = (k3_xboole_0 @ sk_A @ sk_B)))),
% 59.52/59.73      inference('sup-', [status(thm)], ['28', '29'])).
% 59.52/59.73  thf('31', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 59.52/59.73      inference('simplify', [status(thm)], ['30'])).
% 59.52/59.73  thf('32', plain, (((sk_B) = (sk_A))),
% 59.52/59.73      inference('sup+', [status(thm)], ['23', '31'])).
% 59.52/59.73  thf('33', plain, (((sk_A) != (sk_B))),
% 59.52/59.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.52/59.73  thf('34', plain, ($false),
% 59.52/59.73      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 59.52/59.73  
% 59.52/59.73  % SZS output end Refutation
% 59.52/59.73  
% 59.52/59.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
