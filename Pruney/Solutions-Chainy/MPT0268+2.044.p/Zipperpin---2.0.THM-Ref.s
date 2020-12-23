%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jaOUbbDKGw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:58 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  419 ( 554 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
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

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X11 @ X12 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
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

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r2_hidden @ C @ A )
        | ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ( r2_hidden @ X37 @ X35 )
      | ( r1_tarski @ X35 @ ( k4_xboole_0 @ X36 @ ( k1_tarski @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[l2_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jaOUbbDKGw
% 0.16/0.38  % Computer   : n019.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 19:35:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 171 iterations in 0.062s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.24/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.24/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.24/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(t65_zfmisc_1, conjecture,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.24/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i,B:$i]:
% 0.24/0.55        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.24/0.55          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.24/0.55  thf('0', plain,
% 0.24/0.55      (((r2_hidden @ sk_B @ sk_A)
% 0.24/0.55        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('1', plain,
% 0.24/0.55      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.24/0.55       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf(t69_enumset1, axiom,
% 0.24/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.24/0.55  thf('2', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.24/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.24/0.55  thf(t70_enumset1, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.24/0.55  thf('3', plain,
% 0.24/0.55      (![X26 : $i, X27 : $i]:
% 0.24/0.55         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.24/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.24/0.55  thf(d1_enumset1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.55       ( ![E:$i]:
% 0.24/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.24/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.24/0.55  thf(zf_stmt_2, axiom,
% 0.24/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.24/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.24/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_3, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.24/0.55       ( ![E:$i]:
% 0.24/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.24/0.55  thf('4', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.55         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.24/0.55          | (r2_hidden @ X18 @ X22)
% 0.24/0.55          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.24/0.55  thf('5', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.55         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.24/0.55          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.24/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.24/0.55  thf('6', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.24/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['3', '5'])).
% 0.24/0.55  thf('7', plain,
% 0.24/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.55         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.24/0.55         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.24/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.24/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.24/0.55  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['2', '9'])).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.24/0.55        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('12', plain,
% 0.24/0.55      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.24/0.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.24/0.55      inference('split', [status(esa)], ['11'])).
% 0.24/0.55  thf(t79_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.55  thf('13', plain,
% 0.24/0.55      (![X11 : $i, X12 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X11 @ X12) @ X12)),
% 0.24/0.55      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.24/0.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['12', '13'])).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf(t3_xboole_0, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.24/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X2 @ X0)
% 0.24/0.55          | ~ (r2_hidden @ X2 @ X3)
% 0.24/0.55          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.24/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0)))
% 0.24/0.55         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.24/0.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.24/0.55             ((r2_hidden @ sk_B @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['14', '17'])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.24/0.55       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['10', '18'])).
% 0.24/0.55  thf('20', plain,
% 0.24/0.55      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.24/0.55       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['11'])).
% 0.24/0.55  thf(d10_xboole_0, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.24/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.55  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.24/0.55      inference('simplify', [status(thm)], ['21'])).
% 0.24/0.55  thf(l2_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.24/0.55       ( ( r2_hidden @ C @ A ) | 
% 0.24/0.55         ( r1_tarski @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) ) ))).
% 0.24/0.55  thf('23', plain,
% 0.24/0.55      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.24/0.55         (~ (r1_tarski @ X35 @ X36)
% 0.24/0.55          | (r2_hidden @ X37 @ X35)
% 0.24/0.55          | (r1_tarski @ X35 @ (k4_xboole_0 @ X36 @ (k1_tarski @ X37))))),
% 0.24/0.55      inference('cnf', [status(esa)], [l2_zfmisc_1])).
% 0.24/0.55  thf('24', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.24/0.55          | (r2_hidden @ X1 @ X0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.55  thf(t36_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.24/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.24/0.55  thf('26', plain,
% 0.24/0.55      (![X4 : $i, X6 : $i]:
% 0.24/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.24/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.55  thf('27', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.24/0.55          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.55  thf('28', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r2_hidden @ X0 @ X1)
% 0.24/0.55          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['24', '27'])).
% 0.24/0.55  thf('29', plain,
% 0.24/0.55      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.24/0.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.24/0.55      inference('split', [status(esa)], ['0'])).
% 0.24/0.55  thf('30', plain,
% 0.24/0.55      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.24/0.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.55  thf('31', plain,
% 0.24/0.55      (((r2_hidden @ sk_B @ sk_A))
% 0.24/0.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.24/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.24/0.55  thf('32', plain,
% 0.24/0.55      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['11'])).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.24/0.55       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.55  thf('34', plain, ($false),
% 0.24/0.55      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '33'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
