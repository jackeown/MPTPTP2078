%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPjG8ZTh7H

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:28:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  326 ( 578 expanded)
%              Number of equality atoms :   44 (  73 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t6_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t6_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X55: $i,X56: $i] :
      ( ( X56
        = ( k1_tarski @ X55 ) )
      | ( X56 = k1_xboole_0 )
      | ~ ( r1_tarski @ X56 @ ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( X25 = X22 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X22: $i,X25: $i] :
      ( ( X25 = X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('13',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_B_1 = sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X23 != X22 )
      | ( r2_hidden @ X23 @ X24 )
      | ( X24
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('17',plain,(
    ! [X22: $i] :
      ( r2_hidden @ X22 @ ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','29'])).

thf('33',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sup-',[status(thm)],['18','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPjG8ZTh7H
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:06:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 80 iterations in 0.033s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t7_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf(t6_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.49       ( ( A ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.20/0.49          ( ( A ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t6_zfmisc_1])).
% 0.20/0.49  thf('1', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l3_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X55 : $i, X56 : $i]:
% 0.20/0.49         (((X56) = (k1_tarski @ X55))
% 0.20/0.49          | ((X56) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ X56 @ (k1_tarski @ X55)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(d1_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X25 @ X24)
% 0.20/0.49          | ((X25) = (X22))
% 0.20/0.49          | ((X24) != (k1_tarski @ X22)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X22 : $i, X25 : $i]:
% 0.20/0.49         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.49          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (sk_B_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1))
% 0.20/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((((sk_B @ (k1_tarski @ sk_A)) = (sk_B_1))
% 0.20/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.20/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X22 : $i, X25 : $i]:
% 0.20/0.49         (((X25) = (X22)) | ~ (r2_hidden @ X25 @ (k1_tarski @ X22)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_B_1) = (sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         (((X23) != (X22))
% 0.20/0.49          | (r2_hidden @ X23 @ X24)
% 0.20/0.49          | ((X24) != (k1_tarski @ X22)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.49  thf('17', plain, (![X22 : $i]: (r2_hidden @ X22 @ (k1_tarski @ X22))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.49  thf('20', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.49           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf(d5_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.49       ( ![D:$i]:
% 0.20/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.49          | (r2_hidden @ X4 @ X1)
% 0.20/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['25', '29'])).
% 0.20/0.49  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['25', '29'])).
% 0.20/0.49  thf('33', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain, ($false), inference('sup-', [status(thm)], ['18', '33'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
