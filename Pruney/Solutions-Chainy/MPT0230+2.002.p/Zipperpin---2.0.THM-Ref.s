%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8BeRwcYXkL

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  347 ( 402 expanded)
%              Number of equality atoms :   47 (  56 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k2_tarski @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('12',plain,(
    ! [X75: $i,X76: $i,X77: $i] :
      ( ( k1_enumset1 @ X75 @ X77 @ X76 )
      = ( k1_enumset1 @ X75 @ X76 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('13',plain,
    ( ( k1_enumset1 @ sk_B @ sk_A @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['8','11','12'])).

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

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X22 )
      | ( X24 = X23 )
      | ( X24 = X20 )
      | ( X22
       != ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X20: $i,X23: $i,X24: $i] :
      ( ( X24 = X20 )
      | ( X24 = X23 )
      | ~ ( r2_hidden @ X24 @ ( k2_tarski @ X23 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8BeRwcYXkL
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:48:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 156 iterations in 0.078s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(t25_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.54          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.20/0.54             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t28_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.54         = (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf(t22_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.20/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.20/0.54         = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.54         = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.54  thf(t43_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.54       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X30 @ X31 @ X32)
% 0.20/0.54           = (k2_xboole_0 @ (k2_tarski @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1))
% 0.20/0.54           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf(t98_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X75 : $i, X76 : $i, X77 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X75 @ X77 @ X76) = (k1_enumset1 @ X75 @ X76 @ X77))),
% 0.20/0.54      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (((k1_enumset1 @ sk_B @ sk_A @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['8', '11', '12'])).
% 0.20/0.54  thf(d1_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_2, axiom,
% 0.20/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_3, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.20/0.54          | (r2_hidden @ X13 @ X17)
% 0.20/0.54          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.54         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.20/0.54          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.20/0.54          | (zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '15'])).
% 0.20/0.54  thf(d2_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.54       ( ![D:$i]:
% 0.20/0.54         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X20 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X24 @ X22)
% 0.20/0.54          | ((X24) = (X23))
% 0.20/0.54          | ((X24) = (X20))
% 0.20/0.54          | ((X22) != (k2_tarski @ X23 @ X20)))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X20 : $i, X23 : $i, X24 : $i]:
% 0.20/0.54         (((X24) = (X20))
% 0.20/0.54          | ((X24) = (X23))
% 0.20/0.54          | ~ (r2_hidden @ X24 @ (k2_tarski @ X23 @ X20)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X0 @ sk_C @ sk_A @ sk_B)
% 0.20/0.54          | ((X0) = (sk_B))
% 0.20/0.54          | ((X0) = (sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.54         (((X9) != (X11)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X11 @ X10 @ X11 @ X8)),
% 0.20/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.54  thf('22', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.54  thf('23', plain, (((sk_A) != (sk_B))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('24', plain, (((sk_A) != (sk_C))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('25', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['22', '23', '24'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.35/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
