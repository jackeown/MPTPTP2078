%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CmZL6zdxz9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 118 expanded)
%              Number of leaves         :   16 (  41 expanded)
%              Depth                    :   12
%              Number of atoms          :  280 ( 971 expanded)
%              Number of equality atoms :   43 ( 196 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X39 @ X40 ) )
      = ( k2_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
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
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k2_xboole_0 @ X3 @ ( k2_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('16',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k3_tarski @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('24',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37
        = ( k1_tarski @ X36 ) )
      | ( X37 = k1_xboole_0 )
      | ~ ( r1_tarski @ X37 @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_B ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CmZL6zdxz9
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:38:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 64 iterations in 0.034s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('0', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(l51_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X39 : $i, X40 : $i]:
% 0.22/0.49         ((k3_tarski @ (k2_tarski @ X39 @ X40)) = (k2_xboole_0 @ X39 @ X40))),
% 0.22/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(t44_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.49          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.22/0.49             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.22/0.49  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t7_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.49  thf('6', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.22/0.49      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf(l3_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         (((X37) = (k1_tarski @ X36))
% 0.22/0.49          | ((X37) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('8', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '10'])).
% 0.22/0.49  thf(t4_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.49       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k2_xboole_0 @ X3 @ X4) @ X5)
% 0.22/0.49           = (k2_xboole_0 @ X3 @ (k2_xboole_0 @ X4 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ sk_B @ X0)
% 0.22/0.49           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (((k2_xboole_0 @ sk_B @ sk_C)
% 0.22/0.49         = (k2_xboole_0 @ sk_B @ (k3_tarski @ (k1_tarski @ sk_C))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['2', '13'])).
% 0.22/0.49  thf('15', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['3', '10'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (((sk_B) = (k2_xboole_0 @ sk_B @ (k3_tarski @ (k1_tarski @ sk_C))))),
% 0.22/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ sk_B @ X0)
% 0.22/0.49           = (k2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.22/0.49  thf(t10_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (r1_tarski @ X1 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X0 : $i]: (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['17', '20'])).
% 0.22/0.49  thf('22', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.22/0.49      inference('sup+', [status(thm)], ['16', '21'])).
% 0.22/0.49  thf('23', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         (((X37) = (k1_tarski @ X36))
% 0.22/0.49          | ((X37) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X37 @ (k1_tarski @ X36)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.49          | ((X0) = (k1_xboole_0))
% 0.22/0.49          | ((X0) = (k1_tarski @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain, (((sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain, ((((sk_C) = (sk_B)) | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '27'])).
% 0.22/0.49  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain, (((sk_B) != (sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29', '30'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
