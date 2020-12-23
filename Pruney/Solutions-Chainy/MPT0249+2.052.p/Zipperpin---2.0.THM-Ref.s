%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6bn4BKfrzq

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  88 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 ( 697 expanded)
%              Number of equality atoms :   39 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('5',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ sk_C_1 @ sk_B ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6bn4BKfrzq
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 304 iterations in 0.102s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(t44_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.57          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.57             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.57  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t46_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         ((k4_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(l32_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((r1_tarski @ X10 @ X11)
% 0.21/0.57          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.57        | (r1_tarski @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.57  thf(l3_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (((X22) = (k1_tarski @ X21))
% 0.21/0.57          | ((X22) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.57  thf('8', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '10'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf(d3_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.57       ( ![D:$i]:
% 0.21/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.57           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.57          | (r2_hidden @ X4 @ X6)
% 0.21/0.57          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.21/0.57         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.57      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_tarski @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X1 : $i, X3 : $i]:
% 0.21/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.57          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.57  thf('19', plain, ((r1_tarski @ sk_C_1 @ sk_B)),
% 0.21/0.57      inference('sup+', [status(thm)], ['11', '18'])).
% 0.21/0.57  thf('20', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         (((X22) = (k1_tarski @ X21))
% 0.21/0.57          | ((X22) = (k1_xboole_0))
% 0.21/0.57          | ~ (r1_tarski @ X22 @ (k1_tarski @ X21)))),
% 0.21/0.57      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | ((X0) = (k1_xboole_0))
% 0.21/0.57          | ((X0) = (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.21/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain, ((((sk_C_1) = (sk_B)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.57  thf('26', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('27', plain, (((sk_B) != (sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('28', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['25', '26', '27'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
