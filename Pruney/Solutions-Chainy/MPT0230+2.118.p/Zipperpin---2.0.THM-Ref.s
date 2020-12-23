%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aXKSQuEkM

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   49 (  55 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  346 ( 414 expanded)
%              Number of equality atoms :   44 (  54 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X26: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X28 )
        = ( k1_tarski @ X26 ) )
      | ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X26: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ X28 )
        = ( k1_tarski @ X26 ) )
      | ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 != X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X29 ) )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('11',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X29 ) )
     != ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('25',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aXKSQuEkM
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 81 iterations in 0.043s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(d1_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, axiom,
% 0.21/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.21/0.50          | ((X5) = (X6))
% 0.21/0.50          | ((X5) = (X7))
% 0.21/0.50          | ((X5) = (X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t25_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.50          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.50             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf(t28_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.21/0.50         = (k1_tarski @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(l33_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X26 : $i, X28 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ (k1_tarski @ X26) @ X28) = (k1_tarski @ X26))
% 0.21/0.50          | (r2_hidden @ X26 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.50  thf(t48_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.50           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X26 @ X27)
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X26) @ X27) != (k1_tarski @ X26)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.21/0.50          | (r2_hidden @ X0 @ X1)
% 0.21/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X26 : $i, X28 : $i]:
% 0.21/0.50         (((k4_xboole_0 @ (k1_tarski @ X26) @ X28) = (k1_tarski @ X26))
% 0.21/0.50          | (r2_hidden @ X26 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.21/0.50  thf(t20_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.50         ( k1_tarski @ A ) ) <=>
% 0.21/0.50       ( ( A ) != ( B ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         (((X30) != (X29))
% 0.21/0.50          | ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X29))
% 0.21/0.50              != (k1_tarski @ X30)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X29 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X29))
% 0.21/0.50           != (k1_tarski @ X29))),
% 0.21/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.21/0.50          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.50  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ X1)
% 0.21/0.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.50        | (r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '14'])).
% 0.21/0.50  thf('16', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf(t70_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.50       ( ![E:$i]:
% 0.21/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X14 @ X13)
% 0.21/0.50          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.21/0.50          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.21/0.50         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.21/0.50          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.50          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.50  thf('21', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_B @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '21'])).
% 0.21/0.50  thf('23', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.50  thf('24', plain, (((sk_A) != (sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('25', plain, (((sk_A) != (sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('26', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['23', '24', '25'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
