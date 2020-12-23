%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfO7EgSPa1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  55 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  356 ( 412 expanded)
%              Number of equality atoms :   40 (  48 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X11 ) )
      | ( r2_hidden @ X8 @ X11 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ( r2_hidden @ X27 @ X28 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('14',plain,(
    ! [X26: $i,X29: $i] :
      ( r2_hidden @ X26 @ ( k2_tarski @ X29 @ X26 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfO7EgSPa1
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 133 iterations in 0.073s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(d1_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.56       ( ![E:$i]:
% 0.21/0.56         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.56           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, axiom,
% 0.21/0.56    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.56     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.56       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.21/0.56          | ((X15) = (X16))
% 0.21/0.56          | ((X15) = (X17))
% 0.21/0.56          | ((X15) = (X18)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t59_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.21/0.56          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_1, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.56        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.21/0.56             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.21/0.56  thf('1', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf(t1_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.21/0.56         ((r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X11))
% 0.21/0.56          | (r2_hidden @ X8 @ X11)
% 0.21/0.56          | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ sk_B @ X0)
% 0.21/0.56          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_tarski @ sk_A))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf(t100_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X12 @ X13)
% 0.21/0.56           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (((k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.56         = (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf(d5_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X6 @ X5)
% 0.21/0.56          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.56          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X6 @ X4)
% 0.21/0.56          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.56        | ~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '11'])).
% 0.21/0.56  thf(d2_tarski, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.56         (((X27) != (X26))
% 0.21/0.56          | (r2_hidden @ X27 @ X28)
% 0.21/0.56          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X26 : $i, X29 : $i]: (r2_hidden @ X26 @ (k2_tarski @ X29 @ X26))),
% 0.21/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.56  thf('15', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['12', '14'])).
% 0.21/0.56  thf(t70_enumset1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X33 : $i, X34 : $i]:
% 0.21/0.56         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.56  thf(t69_enumset1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.56  thf(zf_stmt_3, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.56       ( ![E:$i]:
% 0.21/0.56         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X24 @ X23)
% 0.21/0.56          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.21/0.56          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.21/0.56         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.21/0.56          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.21/0.56          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['18', '20'])).
% 0.21/0.56  thf('22', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '22'])).
% 0.21/0.56  thf('24', plain, (((sk_B) = (sk_A))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf('25', plain, (((sk_A) != (sk_B))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.56  thf('26', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
