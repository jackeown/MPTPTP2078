%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.weRnOtVtql

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:40 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  406 ( 508 expanded)
%              Number of equality atoms :   45 (  59 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X30 @ ( k1_tarski @ X29 ) )
        = ( k1_tarski @ X29 ) )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X30 @ ( k1_tarski @ X29 ) )
        = ( k1_tarski @ X29 ) )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( ( k3_xboole_0 @ X28 @ ( k1_tarski @ X27 ) )
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('21',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.weRnOtVtql
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 544 iterations in 0.644s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.91/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.91/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.10  thf(d1_enumset1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.10     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.10       ( ![E:$i]:
% 0.91/1.10         ( ( r2_hidden @ E @ D ) <=>
% 0.91/1.10           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, axiom,
% 0.91/1.10    (![E:$i,C:$i,B:$i,A:$i]:
% 0.91/1.10     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.91/1.10       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.91/1.10  thf('0', plain,
% 0.91/1.10      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.10         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.91/1.10          | ((X6) = (X7))
% 0.91/1.10          | ((X6) = (X8))
% 0.91/1.10          | ((X6) = (X9)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(t70_enumset1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X18 : $i, X19 : $i]:
% 0.91/1.10         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.91/1.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.10  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.91/1.10  thf(zf_stmt_2, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.10     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.10       ( ![E:$i]:
% 0.91/1.10         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.10         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.91/1.10          | (r2_hidden @ X10 @ X14)
% 0.91/1.10          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.91/1.10         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.91/1.10          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.91/1.10      inference('simplify', [status(thm)], ['2'])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.10          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.10      inference('sup+', [status(thm)], ['1', '3'])).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.91/1.10         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.91/1.10      inference('simplify', [status(thm)], ['5'])).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['4', '6'])).
% 0.91/1.10  thf(l31_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( r2_hidden @ A @ B ) =>
% 0.91/1.10       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X29 : $i, X30 : $i]:
% 0.91/1.10         (((k3_xboole_0 @ X30 @ (k1_tarski @ X29)) = (k1_tarski @ X29))
% 0.91/1.10          | ~ (r2_hidden @ X29 @ X30))),
% 0.91/1.10      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 0.91/1.10           = (k1_tarski @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.10  thf(t59_zfmisc_1, conjecture,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.91/1.10          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_3, negated_conjecture,
% 0.91/1.10    (~( ![A:$i,B:$i,C:$i]:
% 0.91/1.10        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.91/1.10             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.10  thf(commutativity_k3_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.91/1.10      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf(t16_xboole_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.10       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.10         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.91/1.10           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.91/1.10           = (k3_xboole_0 @ sk_C @ 
% 0.91/1.10              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.91/1.10         = (k3_xboole_0 @ sk_C @ (k1_tarski @ sk_B)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['9', '14'])).
% 0.91/1.10  thf('16', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X29 : $i, X30 : $i]:
% 0.91/1.10         (((k3_xboole_0 @ X30 @ (k1_tarski @ X29)) = (k1_tarski @ X29))
% 0.91/1.10          | ~ (r2_hidden @ X29 @ X30))),
% 0.91/1.10      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.91/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.91/1.10         = (k1_tarski @ sk_B))),
% 0.91/1.10      inference('demod', [status(thm)], ['15', '18'])).
% 0.91/1.10  thf(l29_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.91/1.10       ( r2_hidden @ B @ A ) ))).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X27 : $i, X28 : $i]:
% 0.91/1.10         ((r2_hidden @ X27 @ X28)
% 0.91/1.10          | ((k3_xboole_0 @ X28 @ (k1_tarski @ X27)) != (k1_tarski @ X27)))),
% 0.91/1.10      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.91/1.10        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('22', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.91/1.10      inference('simplify', [status(thm)], ['21'])).
% 0.91/1.10  thf(t69_enumset1, axiom,
% 0.91/1.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.91/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X18 : $i, X19 : $i]:
% 0.91/1.10         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.91/1.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X15 @ X14)
% 0.91/1.10          | ~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.91/1.10          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.91/1.10         (~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.91/1.10          | ~ (r2_hidden @ X15 @ (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['25'])).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.10          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['24', '26'])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.91/1.10          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['23', '27'])).
% 0.91/1.10  thf('29', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.91/1.10      inference('sup-', [status(thm)], ['22', '28'])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['0', '29'])).
% 0.91/1.10  thf('31', plain, (((sk_B) = (sk_A))),
% 0.91/1.10      inference('simplify', [status(thm)], ['30'])).
% 0.91/1.10  thf('32', plain, (((sk_A) != (sk_B))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.10  thf('33', plain, ($false),
% 0.91/1.10      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
