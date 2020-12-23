%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.riROppo078

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:00 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   38 (  77 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 629 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['1'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('11',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t38_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t38_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.riROppo078
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 91 iterations in 0.058s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(d5_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i]:
% 0.33/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.33/0.52       ( ![D:$i]:
% 0.33/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.33/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.33/0.52         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.33/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.33/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.33/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.33/0.52         (((X9) = (k4_xboole_0 @ X5 @ X6))
% 0.33/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.33/0.52          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.33/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.33/0.52          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.33/0.52      inference('eq_fact', [status(thm)], ['1'])).
% 0.33/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.33/0.52  thf('3', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.33/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.33/0.52  thf(d3_tarski, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.33/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.33/0.52          | (r2_hidden @ X0 @ X2)
% 0.33/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.33/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.33/0.52          | ~ (r2_hidden @ X8 @ X6)
% 0.33/0.52          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.33/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (![X0 : $i, X2 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))
% 0.33/0.52          | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ X2 @ k1_xboole_0) @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['6', '8'])).
% 0.33/0.52  thf('10', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.33/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['2', '5'])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.33/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.33/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.33/0.52  thf('13', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.33/0.52  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.33/0.52      inference('condensation', [status(thm)], ['13'])).
% 0.33/0.52  thf('15', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.33/0.52          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.33/0.52      inference('sup-', [status(thm)], ['0', '14'])).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      (![X2 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X2))),
% 0.33/0.52      inference('clc', [status(thm)], ['9', '10'])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]:
% 0.33/0.52         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.33/0.52          | ((X1) = (k1_xboole_0)))),
% 0.33/0.52      inference('demod', [status(thm)], ['15', '16'])).
% 0.33/0.52  thf(t38_xboole_1, conjecture,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.33/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i,B:$i]:
% 0.33/0.52        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.33/0.52          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t38_xboole_1])).
% 0.33/0.52  thf('18', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_A))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.33/0.52          | (r2_hidden @ X0 @ X2)
% 0.33/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.33/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.33/0.52  thf('20', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_A))
% 0.33/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.33/0.52  thf('21', plain,
% 0.33/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.33/0.52         (~ (r2_hidden @ X8 @ X6)
% 0.33/0.52          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.33/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.33/0.52  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.33/0.52      inference('clc', [status(thm)], ['20', '21'])).
% 0.33/0.52  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.33/0.52  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('25', plain, ($false),
% 0.33/0.52      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
