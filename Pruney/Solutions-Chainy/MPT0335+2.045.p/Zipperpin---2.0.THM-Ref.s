%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bhnlps7DnY

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:18 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  353 ( 537 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('16',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['9','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['8','23'])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bhnlps7DnY
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.29/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.29/1.49  % Solved by: fo/fo7.sh
% 1.29/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.49  % done 2090 iterations in 1.046s
% 1.29/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.29/1.49  % SZS output start Refutation
% 1.29/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.29/1.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.29/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.29/1.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.29/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.49  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.29/1.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.29/1.49  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.49  thf(t148_zfmisc_1, conjecture,
% 1.29/1.49    (![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.49     ( ( ( r1_tarski @ A @ B ) & 
% 1.29/1.49         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.29/1.49         ( r2_hidden @ D @ A ) ) =>
% 1.29/1.49       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.29/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.29/1.49        ( ( ( r1_tarski @ A @ B ) & 
% 1.29/1.49            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.29/1.49            ( r2_hidden @ D @ A ) ) =>
% 1.29/1.49          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.29/1.49    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.29/1.49  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(t12_xboole_1, axiom,
% 1.29/1.49    (![A:$i,B:$i]:
% 1.29/1.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.29/1.49  thf('2', plain,
% 1.29/1.49      (![X6 : $i, X7 : $i]:
% 1.29/1.49         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.29/1.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.29/1.49  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.29/1.49      inference('sup-', [status(thm)], ['1', '2'])).
% 1.29/1.49  thf(t21_xboole_1, axiom,
% 1.29/1.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.29/1.49  thf('4', plain,
% 1.29/1.49      (![X11 : $i, X12 : $i]:
% 1.29/1.49         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 1.29/1.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.29/1.49  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.29/1.49      inference('sup+', [status(thm)], ['3', '4'])).
% 1.29/1.49  thf(t16_xboole_1, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.29/1.49       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.29/1.49  thf('6', plain,
% 1.29/1.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.29/1.49         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 1.29/1.49           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.29/1.49      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.29/1.49  thf('7', plain,
% 1.29/1.49      (![X0 : $i]:
% 1.29/1.49         ((k3_xboole_0 @ sk_A @ X0)
% 1.29/1.49           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.29/1.49      inference('sup+', [status(thm)], ['5', '6'])).
% 1.29/1.49  thf('8', plain,
% 1.29/1.49      (((k3_xboole_0 @ sk_A @ sk_C_1)
% 1.29/1.49         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.29/1.49      inference('sup+', [status(thm)], ['0', '7'])).
% 1.29/1.49  thf('9', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf(d4_xboole_0, axiom,
% 1.29/1.49    (![A:$i,B:$i,C:$i]:
% 1.29/1.49     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.29/1.49       ( ![D:$i]:
% 1.29/1.49         ( ( r2_hidden @ D @ C ) <=>
% 1.29/1.49           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.29/1.49  thf('10', plain,
% 1.29/1.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.29/1.49         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.29/1.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.29/1.49          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.29/1.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.29/1.49  thf('11', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.29/1.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.49      inference('eq_fact', [status(thm)], ['10'])).
% 1.29/1.49  thf(d1_tarski, axiom,
% 1.29/1.49    (![A:$i,B:$i]:
% 1.29/1.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.29/1.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.29/1.49  thf('12', plain,
% 1.29/1.49      (![X27 : $i, X29 : $i, X30 : $i]:
% 1.29/1.49         (~ (r2_hidden @ X30 @ X29)
% 1.29/1.49          | ((X30) = (X27))
% 1.29/1.49          | ((X29) != (k1_tarski @ X27)))),
% 1.29/1.49      inference('cnf', [status(esa)], [d1_tarski])).
% 1.29/1.49  thf('13', plain,
% 1.29/1.49      (![X27 : $i, X30 : $i]:
% 1.29/1.49         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 1.29/1.49      inference('simplify', [status(thm)], ['12'])).
% 1.29/1.49  thf('14', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.29/1.49          | ((sk_D @ (k1_tarski @ X0) @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['11', '13'])).
% 1.29/1.49  thf('15', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.29/1.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.49      inference('eq_fact', [status(thm)], ['10'])).
% 1.29/1.49  thf('16', plain,
% 1.29/1.49      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.29/1.49         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.29/1.49      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.29/1.49  thf('17', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.29/1.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['15', '16'])).
% 1.29/1.49  thf('18', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.29/1.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.49      inference('simplify', [status(thm)], ['17'])).
% 1.29/1.49  thf('19', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.29/1.49          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.29/1.49      inference('eq_fact', [status(thm)], ['10'])).
% 1.29/1.49  thf('20', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.29/1.49          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.29/1.49      inference('clc', [status(thm)], ['18', '19'])).
% 1.29/1.49  thf('21', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (~ (r2_hidden @ X0 @ X1)
% 1.29/1.49          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.29/1.49          | ((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 1.29/1.49      inference('sup-', [status(thm)], ['14', '20'])).
% 1.29/1.49  thf('22', plain,
% 1.29/1.49      (![X0 : $i, X1 : $i]:
% 1.29/1.49         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 1.29/1.49          | ~ (r2_hidden @ X0 @ X1))),
% 1.29/1.49      inference('simplify', [status(thm)], ['21'])).
% 1.29/1.49  thf('23', plain,
% 1.29/1.49      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.29/1.49      inference('sup-', [status(thm)], ['9', '22'])).
% 1.29/1.49  thf('24', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 1.29/1.49      inference('sup+', [status(thm)], ['8', '23'])).
% 1.29/1.49  thf('25', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 1.29/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.49  thf('26', plain, ($false),
% 1.29/1.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 1.29/1.49  
% 1.29/1.49  % SZS output end Refutation
% 1.29/1.49  
% 1.29/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
