%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cTvoC3s1h3

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 100 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  342 ( 863 expanded)
%              Number of equality atoms :   31 (  79 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t46_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t46_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_A @ sk_B ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ o_0_0_xboole_0 )
      = X12 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ X1 @ o_0_0_xboole_0 ) @ X0 )
      | ( o_0_0_xboole_0
        = ( k4_xboole_0 @ o_0_0_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( o_0_0_xboole_0
        = ( k4_xboole_0 @ o_0_0_xboole_0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ X2 @ o_0_0_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ X1 @ o_0_0_xboole_0 ) @ X0 )
      | ( o_0_0_xboole_0
        = ( k4_xboole_0 @ o_0_0_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('17',plain,(
    ! [X2: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ o_0_0_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( o_0_0_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( o_0_0_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ o_0_0_xboole_0 )
      | ( o_0_0_xboole_0
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ o_0_0_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ o_0_0_xboole_0 )
      | ( o_0_0_xboole_0
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(condensation,[status(thm)],['19'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( o_0_0_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cTvoC3s1h3
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 85 iterations in 0.063s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(t46_xboole_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t46_xboole_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.51  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (((k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_A @ sk_B)) != (o_0_0_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(d5_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.51         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.51  thf(t1_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('4', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.51  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X12 : $i]: ((k2_xboole_0 @ X12 @ o_0_0_xboole_0) = (X12))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.51         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ X0)
% 0.21/0.51          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.51      inference('eq_fact', [status(thm)], ['7'])).
% 0.21/0.51  thf(d3_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.51       ( ![D:$i]:
% 0.21/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.51           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X0 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_D_1 @ o_0_0_xboole_0 @ X1 @ o_0_0_xboole_0) @ X0)
% 0.21/0.51          | ((o_0_0_xboole_0) = (k4_xboole_0 @ o_0_0_xboole_0 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.51          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i]:
% 0.21/0.51         (((o_0_0_xboole_0) = (k4_xboole_0 @ o_0_0_xboole_0 @ X2))
% 0.21/0.51          | ~ (r2_hidden @ (sk_D_1 @ o_0_0_xboole_0 @ X2 @ o_0_0_xboole_0) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_D_1 @ o_0_0_xboole_0 @ X1 @ o_0_0_xboole_0) @ X0)
% 0.21/0.51          | ((o_0_0_xboole_0) = (k4_xboole_0 @ o_0_0_xboole_0 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '11'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X2 : $i]: ((o_0_0_xboole_0) = (k4_xboole_0 @ o_0_0_xboole_0 @ X2))),
% 0.21/0.51      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X1 @ o_0_0_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.21/0.51      inference('condensation', [status(thm)], ['19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_D_1 @ o_0_0_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.51          | ((o_0_0_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X3)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (((o_0_0_xboole_0) = (k4_xboole_0 @ X0 @ X1))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ o_0_0_xboole_0 @ X1 @ X0) @ 
% 0.21/0.51             (k2_xboole_0 @ X0 @ X2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.21/0.51         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 0.21/0.51          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (sk_D_1 @ o_0_0_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.21/0.51             o_0_0_xboole_0)
% 0.21/0.51          | ((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (sk_D_1 @ o_0_0_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.21/0.51           o_0_0_xboole_0)
% 0.21/0.51          | ((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.21/0.51      inference('condensation', [status(thm)], ['19'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((o_0_0_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '29'])).
% 0.21/0.51  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.37/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
