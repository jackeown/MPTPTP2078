%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdJub4Q648

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  98 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  275 ( 771 expanded)
%              Number of equality atoms :   32 ( 146 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('5',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X22 ) @ X24 )
      | ~ ( r2_hidden @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( r1_xboole_0 @ X6 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X5 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B = sk_C ),
    inference('sup+',[status(thm)],['8','27'])).

thf('29',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kdJub4Q648
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:16:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 121 iterations in 0.046s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(t44_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.49             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.20/0.49  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t7_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('3', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(l3_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i]:
% 0.20/0.49         (((X28) = (k1_tarski @ X27))
% 0.20/0.49          | ((X28) = (k1_xboole_0))
% 0.20/0.49          | ~ (r1_tarski @ X28 @ (k1_tarski @ X27)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.49  thf('5', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.49  thf('9', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(l27_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X25 : $i, X26 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X22 : $i, X24 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X22) @ X24) | ~ (r2_hidden @ X22 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ sk_B @ X0) | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | (r1_tarski @ sk_B @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.49  thf(t70_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X6 @ X9)
% 0.20/0.49          | ~ (r1_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_xboole_0 @ X0 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.49  thf(t66_xboole_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X5 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.20/0.49  thf('23', plain, (((r1_tarski @ sk_B @ sk_C) | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(t12_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('27', plain, (((k2_xboole_0 @ sk_B @ sk_C) = (sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (((sk_B) = (sk_C))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '27'])).
% 0.20/0.49  thf('29', plain, (((sk_B) != (sk_C))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
