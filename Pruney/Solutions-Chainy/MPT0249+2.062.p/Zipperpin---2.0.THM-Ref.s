%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zZlhS7TMNR

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 100 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  352 ( 913 expanded)
%              Number of equality atoms :   53 ( 185 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

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

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf(t43_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ( C = k1_xboole_0 )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B = k1_xboole_0 ) )
        & ~ ( ( C
              = ( k1_tarski @ A ) )
            & ( B
              = ( k1_tarski @ A ) ) )
        & ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( C
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( B
          = ( k1_tarski @ A ) )
        & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( zip_tseitin_2 @ C @ B @ A )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_tarski @ X16 )
       != ( k2_xboole_0 @ X14 @ X15 ) )
      | ( zip_tseitin_2 @ X15 @ X14 @ X16 )
      | ( zip_tseitin_1 @ X15 @ X14 @ X16 )
      | ( zip_tseitin_0 @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B )
      | ( zip_tseitin_0 @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ X0 )
      | ( zip_tseitin_2 @ sk_C @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B != sk_B )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k1_tarski @ X11 ) )
      | ~ ( zip_tseitin_2 @ X13 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['0','9'])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('23',plain,
    ( ( zip_tseitin_0 @ sk_C @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('27',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zZlhS7TMNR
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 33 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.48  thf(t44_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.48          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.48             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.21/0.48  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t7_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.48  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t39_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (((X3) = (k1_tarski @ X2))
% 0.21/0.48          | ((X3) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X3 @ (k1_tarski @ X2)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 0.21/0.48          | ((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '6'])).
% 0.21/0.48  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.48  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf(t43_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ~( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.48          ( ~( ( ( C ) = ( k1_tarski @ A ) ) & ( ( B ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.48          ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_4, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_5, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_6, axiom,
% 0.21/0.48    (![C:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_7, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.48          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.48         (((k1_tarski @ X16) != (k2_xboole_0 @ X14 @ X15))
% 0.21/0.48          | (zip_tseitin_2 @ X15 @ X14 @ X16)
% 0.21/0.48          | (zip_tseitin_1 @ X15 @ X14 @ X16)
% 0.21/0.48          | (zip_tseitin_0 @ X15 @ X14 @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k1_tarski @ X0) != (sk_B))
% 0.21/0.48          | (zip_tseitin_0 @ sk_C @ sk_B @ X0)
% 0.21/0.48          | (zip_tseitin_1 @ sk_C @ sk_B @ X0)
% 0.21/0.48          | (zip_tseitin_2 @ sk_C @ sk_B @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_B) != (sk_B))
% 0.21/0.48        | (zip_tseitin_2 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_2 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.48         (((X13) = (k1_tarski @ X11)) | ~ (zip_tseitin_2 @ X13 @ X12 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | ((sk_C) = (sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, (((sk_B) != (sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48        | (zip_tseitin_0 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X9 @ X8 @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((zip_tseitin_0 @ sk_C @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((zip_tseitin_0 @ sk_C @ sk_B @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.48         (((X7) = (k1_xboole_0)) | ~ (zip_tseitin_0 @ X7 @ X6 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.48  thf('27', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
