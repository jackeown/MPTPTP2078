%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F97elpdfOb

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:08 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   46 (  72 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  291 ( 579 expanded)
%              Number of equality atoms :   35 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('5',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X23 ) )
      | ( X22
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('9',plain,(
    ! [X20: $i,X23: $i] :
      ( r1_tarski @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X20 @ X23 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t58_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_xboole_0 @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_xboole_0 @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X22
        = ( k2_tarski @ X20 @ X21 ) )
      | ( X22
        = ( k1_tarski @ X21 ) )
      | ( X22
        = ( k1_tarski @ X20 ) )
      | ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18'])).

thf('20',plain,(
    r2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ ( k2_tarski @ X20 @ X23 ) )
      | ( X22
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('22',plain,(
    ! [X20: $i,X23: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X20 @ X23 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t58_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_xboole_0 @ sk_A @ ( k2_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_xboole_0 @ sk_A @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('30',plain,(
    ! [X1: $i] :
      ~ ( r2_xboole_0 @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference('sup-',[status(thm)],['28','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F97elpdfOb
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:32:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 465 iterations in 0.200s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(t66_zfmisc_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.44/0.65          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i]:
% 0.44/0.65        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.44/0.65             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(l32_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.65  thf('1', plain,
% 0.44/0.65      (![X3 : $i, X4 : $i]:
% 0.44/0.65         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.65        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.65  thf('3', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.44/0.65      inference('simplify', [status(thm)], ['2'])).
% 0.44/0.65  thf(d8_xboole_0, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.44/0.65       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X0 : $i, X2 : $i]:
% 0.44/0.65         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.44/0.65      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      ((((sk_A) = (k1_tarski @ sk_B))
% 0.44/0.65        | (r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.65  thf('6', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('7', plain, ((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf(t42_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.44/0.65       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.44/0.65            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         ((r1_tarski @ X22 @ (k2_tarski @ X20 @ X23))
% 0.44/0.65          | ((X22) != (k1_tarski @ X20)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.44/0.65  thf('9', plain,
% 0.44/0.65      (![X20 : $i, X23 : $i]:
% 0.44/0.65         (r1_tarski @ (k1_tarski @ X20) @ (k2_tarski @ X20 @ X23))),
% 0.44/0.65      inference('simplify', [status(thm)], ['8'])).
% 0.44/0.65  thf(t58_xboole_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( r2_xboole_0 @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.65       ( r2_xboole_0 @ A @ C ) ))).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         (~ (r2_xboole_0 @ X14 @ X15)
% 0.44/0.65          | ~ (r1_tarski @ X15 @ X16)
% 0.44/0.65          | (r2_xboole_0 @ X14 @ X16))),
% 0.44/0.65      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.65          | ~ (r2_xboole_0 @ X2 @ (k1_tarski @ X1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X0 : $i]: (r2_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['7', '11'])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.44/0.65  thf('14', plain, (![X0 : $i]: (r1_tarski @ sk_A @ (k2_tarski @ sk_B @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.65         (((X22) = (k2_tarski @ X20 @ X21))
% 0.44/0.65          | ((X22) = (k1_tarski @ X21))
% 0.44/0.65          | ((X22) = (k1_tarski @ X20))
% 0.44/0.65          | ((X22) = (k1_xboole_0))
% 0.44/0.65          | ~ (r1_tarski @ X22 @ (k2_tarski @ X20 @ X21)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_A) = (k1_xboole_0))
% 0.44/0.65          | ((sk_A) = (k1_tarski @ sk_B))
% 0.44/0.65          | ((sk_A) = (k1_tarski @ X0))
% 0.44/0.65          | ((sk_A) = (k2_tarski @ sk_B @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.65  thf('17', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         (((sk_A) = (k1_tarski @ X0)) | ((sk_A) = (k2_tarski @ sk_B @ X0)))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['16', '17', '18'])).
% 0.44/0.65  thf('20', plain, ((r2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (![X20 : $i, X22 : $i, X23 : $i]:
% 0.44/0.65         ((r1_tarski @ X22 @ (k2_tarski @ X20 @ X23))
% 0.44/0.65          | ((X22) != (k1_tarski @ X23)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      (![X20 : $i, X23 : $i]:
% 0.44/0.65         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X20 @ X23))),
% 0.44/0.65      inference('simplify', [status(thm)], ['21'])).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.65         (~ (r2_xboole_0 @ X14 @ X15)
% 0.44/0.65          | ~ (r1_tarski @ X15 @ X16)
% 0.44/0.65          | (r2_xboole_0 @ X14 @ X16))),
% 0.44/0.65      inference('cnf', [status(esa)], [t58_xboole_1])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.65          | ~ (r2_xboole_0 @ X2 @ (k1_tarski @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('25', plain,
% 0.44/0.65      (![X0 : $i]: (r2_xboole_0 @ sk_A @ (k2_tarski @ X0 @ sk_B))),
% 0.44/0.65      inference('sup-', [status(thm)], ['20', '24'])).
% 0.44/0.65  thf('26', plain,
% 0.44/0.65      (((r2_xboole_0 @ sk_A @ sk_A) | ((sk_A) = (k1_tarski @ sk_B)))),
% 0.44/0.65      inference('sup+', [status(thm)], ['19', '25'])).
% 0.44/0.65  thf('27', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('28', plain, ((r2_xboole_0 @ sk_A @ sk_A)),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.44/0.65  thf('29', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (((X0) != (X1)) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.44/0.65      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.44/0.65  thf('30', plain, (![X1 : $i]: ~ (r2_xboole_0 @ X1 @ X1)),
% 0.44/0.65      inference('simplify', [status(thm)], ['29'])).
% 0.44/0.65  thf('31', plain, ($false), inference('sup-', [status(thm)], ['28', '30'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
