%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ryxf6BOaDu

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  227 ( 251 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(t27_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( ( k2_tarski @ A @ B )
        = ( k1_tarski @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( ( k2_tarski @ A @ B )
          = ( k1_tarski @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k1_tarski @ X31 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ( k2_tarski @ sk_A @ sk_B_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = o_0_0_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['16','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ryxf6BOaDu
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:37:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 260 iterations in 0.092s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.55  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.55  thf(t27_zfmisc_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.55       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.20/0.55          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k1_tarski @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(l3_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i]:
% 0.20/0.55         (((X32) = (k1_tarski @ X31))
% 0.20/0.55          | ((X32) = (k1_xboole_0))
% 0.20/0.55          | ~ (r1_tarski @ X32 @ (k1_tarski @ X31)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.55  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.55  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i]:
% 0.20/0.55         (((X32) = (k1_tarski @ X31))
% 0.20/0.55          | ((X32) = (o_0_0_xboole_0))
% 0.20/0.55          | ~ (r1_tarski @ X32 @ (k1_tarski @ X31)))),
% 0.20/0.55      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((((k2_tarski @ sk_A @ sk_B_1) = (o_0_0_xboole_0))
% 0.20/0.55        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.55  thf('5', plain, (((k2_tarski @ sk_A @ sk_B_1) != (k1_tarski @ sk_C_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain, (((k2_tarski @ sk_A @ sk_B_1) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf(t70_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X20 : $i, X21 : $i]:
% 0.20/0.55         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.55  thf(d1_enumset1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_3, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.55       ( ![E:$i]:
% 0.20/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.20/0.55          | (r2_hidden @ X12 @ X16)
% 0.20/0.55          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.55         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.20/0.55          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.20/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.20/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.55  thf(d1_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf('16', plain, (~ (v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '15'])).
% 0.20/0.55  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.20/0.55  thf('17', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.20/0.55  thf('18', plain, ($false), inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
