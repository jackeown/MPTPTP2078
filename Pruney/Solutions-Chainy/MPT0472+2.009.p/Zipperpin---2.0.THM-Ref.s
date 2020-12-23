%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2epeIgdvrP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 387 expanded)
%              Number of equality atoms :   30 (  75 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('3',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_A_1 ) )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('4',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
   <= ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','8','9'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('13',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_A_1 ) )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','7'])).

thf('15',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k1_relat_1 @ sk_A_1 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_A_1 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ sk_A_1 ),
    inference(simpl_trail,[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    sk_A_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2epeIgdvrP
% 0.14/0.37  % Computer   : n003.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:22:12 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 13 iterations in 0.009s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(t64_relat_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( v1_relat_1 @ A ) =>
% 0.22/0.49          ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49              ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.49            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t64_relat_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))
% 0.22/0.49        | ((k2_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(fc9_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.49       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X2 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ (k2_relat_1 @ X2))
% 0.22/0.49          | ~ (v1_relat_1 @ X2)
% 0.22/0.49          | (v1_xboole_0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.49         | (v1_xboole_0 @ sk_A_1)
% 0.22/0.49         | ~ (v1_relat_1 @ sk_A_1)))
% 0.22/0.49         <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.22/0.49  thf('4', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.22/0.49  thf('5', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.22/0.49  thf(l13_xboole_0, axiom,
% 0.22/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.49  thf('7', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.49  thf('9', plain, ((v1_relat_1 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_A_1)) <= ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(fc8_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.49       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X1 : $i]:
% 0.22/0.49         (~ (v1_xboole_0 @ (k1_relat_1 @ X1))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.49         | (v1_xboole_0 @ sk_A_1)
% 0.22/0.49         | ~ (v1_relat_1 @ sk_A_1)))
% 0.22/0.49         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.49      inference('demod', [status(thm)], ['4', '7'])).
% 0.22/0.49  thf('15', plain, ((v1_relat_1 @ sk_A_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_A_1)) <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((sk_A_1) = (k1_xboole_0)))
% 0.22/0.49         <= ((((k1_relat_1 @ sk_A_1) = (k1_xboole_0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain, (~ (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0))) | 
% 0.22/0.49       (((k1_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('22', plain, ((((k2_relat_1 @ sk_A_1) = (k1_xboole_0)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain, ((v1_xboole_0 @ sk_A_1)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['10', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.49  thf('25', plain, (((sk_A_1) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
