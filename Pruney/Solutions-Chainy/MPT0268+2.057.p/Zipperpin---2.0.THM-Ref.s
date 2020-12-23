%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uV8imOo17A

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  438 ( 626 expanded)
%              Number of equality atoms :   37 (  52 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( ( sk_A != sk_A )
      | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uV8imOo17A
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 361 iterations in 0.165s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(t65_zfmisc_1, conjecture,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.37/0.61       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i,B:$i]:
% 0.37/0.61        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.37/0.61          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (((r2_hidden @ sk_B @ sk_A)
% 0.37/0.61        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.37/0.61       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf(t69_enumset1, axiom,
% 0.37/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.61  thf('2', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.37/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.61  thf(t70_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i]:
% 0.37/0.61         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.37/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.61  thf(d1_enumset1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.61       ( ![E:$i]:
% 0.37/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.61  thf(zf_stmt_2, axiom,
% 0.37/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_3, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.61       ( ![E:$i]:
% 0.37/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.61         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.37/0.61          | (r2_hidden @ X14 @ X18)
% 0.37/0.61          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.37/0.61          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.37/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.61      inference('sup+', [status(thm)], ['3', '5'])).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.37/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '8'])).
% 0.37/0.61  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['2', '9'])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.37/0.61        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.37/0.61         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.61      inference('split', [status(esa)], ['11'])).
% 0.37/0.61  thf(t83_xboole_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.61  thf('13', plain,
% 0.37/0.61      (![X6 : $i, X8 : $i]:
% 0.37/0.61         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))
% 0.37/0.61         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.37/0.61         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf(t3_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0)))
% 0.37/0.62         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.62  thf('19', plain,
% 0.37/0.62      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.37/0.62         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.37/0.62             ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['15', '18'])).
% 0.37/0.62  thf('20', plain,
% 0.37/0.62      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.37/0.62       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['10', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.37/0.62       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['11'])).
% 0.37/0.62  thf(l27_zfmisc_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X31 : $i, X32 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 0.37/0.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.62  thf('24', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X2 @ X0)
% 0.37/0.62          | ~ (r2_hidden @ X2 @ X3)
% 0.37/0.62          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.62  thf('26', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.62          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.37/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.62          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('sup-', [status(thm)], ['23', '26'])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.62      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['22', '28'])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      (![X6 : $i, X7 : $i]:
% 0.37/0.62         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.37/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         ((r2_hidden @ X0 @ X1)
% 0.37/0.62          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.62  thf('32', plain,
% 0.37/0.62      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.37/0.62         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.62      inference('split', [status(esa)], ['0'])).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.37/0.62         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      (((r2_hidden @ sk_B @ sk_A))
% 0.37/0.62         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.37/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.37/0.62      inference('split', [status(esa)], ['11'])).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.37/0.62       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.62  thf('37', plain, ($false),
% 0.37/0.62      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '36'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
