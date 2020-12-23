%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aIajvfdY9N

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:55 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   71 (  85 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  496 ( 622 expanded)
%              Number of equality atoms :   52 (  66 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aIajvfdY9N
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:19:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.14/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.34  % Solved by: fo/fo7.sh
% 1.14/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.34  % done 1749 iterations in 0.888s
% 1.14/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.34  % SZS output start Refutation
% 1.14/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.14/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.14/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.14/1.34  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.14/1.34  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.14/1.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.14/1.34  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.14/1.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.34  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.14/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.34  thf(t65_zfmisc_1, conjecture,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.14/1.34       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.14/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.34    (~( ![A:$i,B:$i]:
% 1.14/1.34        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.14/1.34          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.14/1.34    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.14/1.34  thf('0', plain,
% 1.14/1.34      (((r2_hidden @ sk_B @ sk_A)
% 1.14/1.34        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('1', plain,
% 1.14/1.34      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.14/1.34       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.14/1.34      inference('split', [status(esa)], ['0'])).
% 1.14/1.34  thf('2', plain,
% 1.14/1.34      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.14/1.34      inference('split', [status(esa)], ['0'])).
% 1.14/1.34  thf(t69_enumset1, axiom,
% 1.14/1.34    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.14/1.34  thf('3', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.14/1.34      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.14/1.34  thf(t70_enumset1, axiom,
% 1.14/1.34    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.14/1.34  thf('4', plain,
% 1.14/1.34      (![X37 : $i, X38 : $i]:
% 1.14/1.34         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.14/1.34      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.14/1.34  thf(d1_enumset1, axiom,
% 1.14/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.34     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.14/1.34       ( ![E:$i]:
% 1.14/1.34         ( ( r2_hidden @ E @ D ) <=>
% 1.14/1.34           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.14/1.34  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.14/1.34  thf(zf_stmt_2, axiom,
% 1.14/1.34    (![E:$i,C:$i,B:$i,A:$i]:
% 1.14/1.34     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.14/1.34       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.14/1.34  thf(zf_stmt_3, axiom,
% 1.14/1.34    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.34     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.14/1.34       ( ![E:$i]:
% 1.14/1.34         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.14/1.34  thf('5', plain,
% 1.14/1.34      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.14/1.34         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 1.14/1.34          | (r2_hidden @ X29 @ X33)
% 1.14/1.34          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.14/1.34  thf('6', plain,
% 1.14/1.34      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.14/1.34         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 1.14/1.34          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 1.14/1.34      inference('simplify', [status(thm)], ['5'])).
% 1.14/1.34  thf('7', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.34         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.14/1.34          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.14/1.34      inference('sup+', [status(thm)], ['4', '6'])).
% 1.14/1.34  thf('8', plain,
% 1.14/1.34      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.14/1.34         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.14/1.34  thf('9', plain,
% 1.14/1.34      (![X24 : $i, X26 : $i, X27 : $i]:
% 1.14/1.34         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 1.14/1.34      inference('simplify', [status(thm)], ['8'])).
% 1.14/1.34  thf('10', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.14/1.34      inference('sup-', [status(thm)], ['7', '9'])).
% 1.14/1.34  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.14/1.34      inference('sup+', [status(thm)], ['3', '10'])).
% 1.14/1.34  thf('12', plain,
% 1.14/1.34      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.14/1.34        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.14/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.34  thf('13', plain,
% 1.14/1.34      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.14/1.34         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('split', [status(esa)], ['12'])).
% 1.14/1.34  thf(d5_xboole_0, axiom,
% 1.14/1.34    (![A:$i,B:$i,C:$i]:
% 1.14/1.34     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.14/1.34       ( ![D:$i]:
% 1.14/1.34         ( ( r2_hidden @ D @ C ) <=>
% 1.14/1.34           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.14/1.34  thf('14', plain,
% 1.14/1.34      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.14/1.34         (~ (r2_hidden @ X6 @ X5)
% 1.14/1.34          | ~ (r2_hidden @ X6 @ X4)
% 1.14/1.34          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.14/1.34      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.14/1.34  thf('15', plain,
% 1.14/1.34      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.14/1.34         (~ (r2_hidden @ X6 @ X4)
% 1.14/1.34          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.14/1.34      inference('simplify', [status(thm)], ['14'])).
% 1.14/1.34  thf('16', plain,
% 1.14/1.34      ((![X0 : $i]:
% 1.14/1.34          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.14/1.34         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['13', '15'])).
% 1.14/1.34  thf('17', plain,
% 1.14/1.34      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.14/1.34         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['11', '16'])).
% 1.14/1.34  thf('18', plain,
% 1.14/1.34      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.14/1.34       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.14/1.34      inference('sup-', [status(thm)], ['2', '17'])).
% 1.14/1.34  thf('19', plain,
% 1.14/1.34      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.14/1.34       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.14/1.34      inference('split', [status(esa)], ['12'])).
% 1.14/1.34  thf(l27_zfmisc_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.14/1.34  thf('20', plain,
% 1.14/1.34      (![X42 : $i, X43 : $i]:
% 1.14/1.34         ((r1_xboole_0 @ (k1_tarski @ X42) @ X43) | (r2_hidden @ X42 @ X43))),
% 1.14/1.34      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.14/1.34  thf(t83_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.14/1.34  thf('21', plain,
% 1.14/1.34      (![X21 : $i, X22 : $i]:
% 1.14/1.34         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 1.14/1.34      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.14/1.34  thf('22', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((r2_hidden @ X1 @ X0)
% 1.14/1.34          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 1.14/1.34      inference('sup-', [status(thm)], ['20', '21'])).
% 1.14/1.34  thf(t48_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.14/1.34  thf('23', plain,
% 1.14/1.34      (![X15 : $i, X16 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 1.14/1.34           = (k3_xboole_0 @ X15 @ X16))),
% 1.14/1.34      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.14/1.34  thf(t36_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.14/1.34  thf('24', plain,
% 1.14/1.34      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.14/1.34      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.14/1.34  thf(l32_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.14/1.34  thf('25', plain,
% 1.14/1.34      (![X8 : $i, X10 : $i]:
% 1.14/1.34         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.14/1.34      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.14/1.34  thf('26', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.14/1.34      inference('sup-', [status(thm)], ['24', '25'])).
% 1.14/1.34  thf('27', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.14/1.34      inference('sup+', [status(thm)], ['23', '26'])).
% 1.14/1.34  thf(t49_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i,C:$i]:
% 1.14/1.34     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.14/1.34       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.14/1.34  thf('28', plain,
% 1.14/1.34      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.14/1.34         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 1.14/1.34           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 1.14/1.34      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.14/1.34  thf('29', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.14/1.34      inference('demod', [status(thm)], ['27', '28'])).
% 1.14/1.34  thf(t100_xboole_1, axiom,
% 1.14/1.34    (![A:$i,B:$i]:
% 1.14/1.34     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.14/1.34  thf('30', plain,
% 1.14/1.34      (![X11 : $i, X12 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ X11 @ X12)
% 1.14/1.34           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.14/1.34      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.14/1.34  thf('31', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.14/1.34           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.14/1.34      inference('sup+', [status(thm)], ['29', '30'])).
% 1.14/1.34  thf(t5_boole, axiom,
% 1.14/1.34    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.14/1.34  thf('32', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 1.14/1.34      inference('cnf', [status(esa)], [t5_boole])).
% 1.14/1.34  thf('33', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.14/1.34      inference('demod', [status(thm)], ['31', '32'])).
% 1.14/1.34  thf('34', plain,
% 1.14/1.34      (![X0 : $i, X1 : $i]:
% 1.14/1.34         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.14/1.34          | (r2_hidden @ X0 @ X1))),
% 1.14/1.34      inference('sup+', [status(thm)], ['22', '33'])).
% 1.14/1.34  thf('35', plain,
% 1.14/1.34      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.14/1.34         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('split', [status(esa)], ['0'])).
% 1.14/1.34  thf('36', plain,
% 1.14/1.34      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 1.14/1.34         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('sup-', [status(thm)], ['34', '35'])).
% 1.14/1.34  thf('37', plain,
% 1.14/1.34      (((r2_hidden @ sk_B @ sk_A))
% 1.14/1.34         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.14/1.34      inference('simplify', [status(thm)], ['36'])).
% 1.14/1.34  thf('38', plain,
% 1.14/1.34      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.14/1.34      inference('split', [status(esa)], ['12'])).
% 1.14/1.34  thf('39', plain,
% 1.14/1.34      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.14/1.34       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.14/1.34      inference('sup-', [status(thm)], ['37', '38'])).
% 1.14/1.34  thf('40', plain, ($false),
% 1.14/1.34      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '39'])).
% 1.14/1.34  
% 1.14/1.34  % SZS output end Refutation
% 1.14/1.34  
% 1.14/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
