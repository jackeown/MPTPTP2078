%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMqRt6xrI2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:20 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 330 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k1_enumset1 @ X49 @ X49 @ X50 )
      = ( k2_tarski @ X49 @ X50 ) ) ),
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

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X31 @ X35 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMqRt6xrI2
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.85  % Solved by: fo/fo7.sh
% 0.66/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.85  % done 836 iterations in 0.394s
% 0.66/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.85  % SZS output start Refutation
% 0.66/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.85  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.66/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.66/0.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.85  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.66/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.85  thf(t47_zfmisc_1, conjecture,
% 0.66/0.85    (![A:$i,B:$i,C:$i]:
% 0.66/0.85     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.66/0.85       ( r2_hidden @ A @ C ) ))).
% 0.66/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.85        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.66/0.85          ( r2_hidden @ A @ C ) ) )),
% 0.66/0.85    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.66/0.85  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf(t70_enumset1, axiom,
% 0.66/0.85    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.66/0.85  thf('1', plain,
% 0.66/0.85      (![X49 : $i, X50 : $i]:
% 0.66/0.85         ((k1_enumset1 @ X49 @ X49 @ X50) = (k2_tarski @ X49 @ X50))),
% 0.66/0.85      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.66/0.85  thf(d1_enumset1, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.85       ( ![E:$i]:
% 0.66/0.85         ( ( r2_hidden @ E @ D ) <=>
% 0.66/0.85           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.66/0.85  thf(zf_stmt_2, axiom,
% 0.66/0.85    (![E:$i,C:$i,B:$i,A:$i]:
% 0.66/0.85     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.66/0.85       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.66/0.85  thf(zf_stmt_3, axiom,
% 0.66/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.85     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.66/0.85       ( ![E:$i]:
% 0.66/0.85         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.66/0.85  thf('2', plain,
% 0.66/0.85      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.66/0.85         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34)
% 0.66/0.85          | (r2_hidden @ X31 @ X35)
% 0.66/0.85          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.66/0.85  thf('3', plain,
% 0.66/0.85      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.66/0.85         ((r2_hidden @ X31 @ (k1_enumset1 @ X34 @ X33 @ X32))
% 0.66/0.85          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34))),
% 0.66/0.85      inference('simplify', [status(thm)], ['2'])).
% 0.66/0.85  thf('4', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.66/0.85          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.66/0.85      inference('sup+', [status(thm)], ['1', '3'])).
% 0.66/0.85  thf('5', plain,
% 0.66/0.85      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.66/0.85         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.66/0.85  thf('6', plain,
% 0.66/0.85      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.66/0.85         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X26)),
% 0.66/0.85      inference('simplify', [status(thm)], ['5'])).
% 0.66/0.85  thf('7', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.66/0.85      inference('sup-', [status(thm)], ['4', '6'])).
% 0.66/0.85  thf(d3_tarski, axiom,
% 0.66/0.85    (![A:$i,B:$i]:
% 0.66/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.85  thf('8', plain,
% 0.66/0.85      (![X3 : $i, X5 : $i]:
% 0.66/0.85         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf(t7_xboole_1, axiom,
% 0.66/0.85    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.85  thf('9', plain,
% 0.66/0.85      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 0.66/0.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.85  thf('10', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X2 @ X3)
% 0.66/0.85          | (r2_hidden @ X2 @ X4)
% 0.66/0.85          | ~ (r1_tarski @ X3 @ X4))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf('11', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.66/0.85      inference('sup-', [status(thm)], ['9', '10'])).
% 0.66/0.85  thf('12', plain,
% 0.66/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.85         ((r1_tarski @ X0 @ X1)
% 0.66/0.85          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['8', '11'])).
% 0.66/0.85  thf('13', plain,
% 0.66/0.85      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.66/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.85  thf('14', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X2 @ X3)
% 0.66/0.85          | (r2_hidden @ X2 @ X4)
% 0.66/0.85          | ~ (r1_tarski @ X3 @ X4))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf('15', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ X0 @ sk_C_1)
% 0.66/0.85          | ~ (r2_hidden @ X0 @ 
% 0.66/0.85               (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.85  thf('16', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ X0)
% 0.66/0.85          | (r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_A @ sk_B)) @ sk_C_1))),
% 0.66/0.85      inference('sup-', [status(thm)], ['12', '15'])).
% 0.66/0.85  thf('17', plain,
% 0.66/0.85      (![X3 : $i, X5 : $i]:
% 0.66/0.85         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf('18', plain,
% 0.66/0.85      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.66/0.85        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.66/0.85      inference('sup-', [status(thm)], ['16', '17'])).
% 0.66/0.85  thf('19', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.66/0.85      inference('simplify', [status(thm)], ['18'])).
% 0.66/0.85  thf('20', plain,
% 0.66/0.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.85         (~ (r2_hidden @ X2 @ X3)
% 0.66/0.85          | (r2_hidden @ X2 @ X4)
% 0.66/0.85          | ~ (r1_tarski @ X3 @ X4))),
% 0.66/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.85  thf('21', plain,
% 0.66/0.85      (![X0 : $i]:
% 0.66/0.85         ((r2_hidden @ X0 @ sk_C_1)
% 0.66/0.85          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.66/0.85      inference('sup-', [status(thm)], ['19', '20'])).
% 0.66/0.85  thf('22', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.66/0.85      inference('sup-', [status(thm)], ['7', '21'])).
% 0.66/0.85  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.66/0.85  
% 0.66/0.85  % SZS output end Refutation
% 0.66/0.85  
% 0.71/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
