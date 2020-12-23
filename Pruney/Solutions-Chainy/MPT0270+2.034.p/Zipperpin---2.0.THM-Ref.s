%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BlT8dxcYZc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:16 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :  464 ( 666 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
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
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

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
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('36',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','27','28','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BlT8dxcYZc
% 0.11/0.33  % Computer   : n010.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 17:13:59 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 228 iterations in 0.110s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.55  thf(t67_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i]:
% 0.37/0.55        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.37/0.55          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.37/0.55  thf('0', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf(t69_enumset1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.55  thf('2', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.37/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.55  thf(t70_enumset1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i]:
% 0.37/0.55         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.37/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.55  thf(d1_enumset1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.55       ( ![E:$i]:
% 0.37/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_2, axiom,
% 0.37/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_3, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.55       ( ![E:$i]:
% 0.37/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.37/0.55          | (r2_hidden @ X16 @ X20)
% 0.37/0.55          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.37/0.55          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.37/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '5'])).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.37/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.37/0.55  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['2', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.37/0.55        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['11'])).
% 0.37/0.55  thf(t83_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      (![X8 : $i, X10 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.37/0.55         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.55  thf(t3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X2 : $i, X3 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ X5)
% 0.37/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.55          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '19'])).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '21'])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ~ (r2_hidden @ X4 @ X5)
% 0.37/0.55          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.37/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.37/0.55         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.37/0.55         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.37/0.55             ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('split', [status(esa)], ['11'])).
% 0.37/0.55  thf(l27_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      (![X33 : $i, X34 : $i]:
% 0.37/0.55         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 0.37/0.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.37/0.55  thf('30', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i]:
% 0.37/0.55         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.37/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r2_hidden @ X1 @ X0)
% 0.37/0.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('split', [status(esa)], ['0'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B))
% 0.37/0.55         <= (~
% 0.37/0.55             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['33'])).
% 0.37/0.55  thf('35', plain,
% 0.37/0.55      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.37/0.55      inference('split', [status(esa)], ['11'])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.37/0.55       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain, ($false),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['1', '27', '28', '36'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
