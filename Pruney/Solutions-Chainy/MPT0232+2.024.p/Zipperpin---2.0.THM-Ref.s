%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYGoFjU14U

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:36 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   47 (  49 expanded)
%              Number of leaves         :   23 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  279 ( 303 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35
        = ( k1_tarski @ X34 ) )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ X35 @ ( k1_tarski @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('2',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['2','3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','11'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VYGoFjU14U
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 171 iterations in 0.149s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(t27_zfmisc_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.43/0.61       ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.43/0.61          ( ( k2_tarski @ A @ B ) = ( k1_tarski @ C ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t27_zfmisc_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(l3_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.43/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X34 : $i, X35 : $i]:
% 0.43/0.61         (((X35) = (k1_tarski @ X34))
% 0.43/0.61          | ((X35) = (k1_xboole_0))
% 0.43/0.61          | ~ (r1_tarski @ X35 @ (k1_tarski @ X34)))),
% 0.43/0.61      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.43/0.61        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.61  thf('3', plain, (((k2_tarski @ sk_A @ sk_B) != (k1_tarski @ sk_C))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('4', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf(t70_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X25 : $i, X26 : $i]:
% 0.43/0.61         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.43/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.61  thf(d1_enumset1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.43/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.61  thf(zf_stmt_2, axiom,
% 0.43/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.43/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.43/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_3, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.61       ( ![E:$i]:
% 0.43/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.61         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.43/0.61          | (r2_hidden @ X17 @ X21)
% 0.43/0.61          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.61         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.43/0.61          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.43/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['5', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.61         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.43/0.61         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.43/0.61      inference('simplify', [status(thm)], ['9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['8', '10'])).
% 0.43/0.61  thf('12', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['4', '11'])).
% 0.43/0.61  thf(idempotence_k2_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.61  thf('13', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 0.43/0.61      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.43/0.61  thf(t7_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.43/0.61  thf('15', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.43/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.43/0.61  thf(l32_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X7 : $i, X9 : $i]:
% 0.43/0.61         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.43/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.43/0.61  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf(d5_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.43/0.61       ( ![D:$i]:
% 0.43/0.61         ( ( r2_hidden @ D @ C ) <=>
% 0.43/0.61           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ X3)
% 0.43/0.61          | ~ (r2_hidden @ X4 @ X2)
% 0.43/0.61          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X4 @ X2)
% 0.43/0.61          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['17', '19'])).
% 0.43/0.61  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.43/0.61      inference('condensation', [status(thm)], ['20'])).
% 0.43/0.61  thf('22', plain, ($false), inference('sup-', [status(thm)], ['12', '21'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
