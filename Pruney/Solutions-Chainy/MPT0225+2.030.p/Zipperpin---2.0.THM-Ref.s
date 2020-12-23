%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kicmaqKUxo

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  564 ( 877 expanded)
%              Number of equality atoms :   67 ( 112 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
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

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k4_xboole_0 @ X6 @ X8 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
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

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

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

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('22',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,
    ( ( sk_A = sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_A != sk_B )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','22','23','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kicmaqKUxo
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:11:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.67  % Solved by: fo/fo7.sh
% 0.19/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.67  % done 495 iterations in 0.226s
% 0.19/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.67  % SZS output start Refutation
% 0.19/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.67  thf(t20_zfmisc_1, conjecture,
% 0.19/0.67    (![A:$i,B:$i]:
% 0.19/0.67     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.67         ( k1_tarski @ A ) ) <=>
% 0.19/0.67       ( ( A ) != ( B ) ) ))).
% 0.19/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.67    (~( ![A:$i,B:$i]:
% 0.19/0.67        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.19/0.67            ( k1_tarski @ A ) ) <=>
% 0.19/0.67          ( ( A ) != ( B ) ) ) )),
% 0.19/0.67    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.19/0.67  thf('0', plain,
% 0.19/0.67      ((((sk_A) = (sk_B))
% 0.19/0.67        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67            != (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.67  thf('1', plain,
% 0.19/0.67      ((((sk_A) = (sk_B))) | 
% 0.19/0.67       ~
% 0.19/0.67       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          = (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('split', [status(esa)], ['0'])).
% 0.19/0.67  thf('2', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.19/0.67      inference('split', [status(esa)], ['0'])).
% 0.19/0.67  thf('3', plain,
% 0.19/0.67      ((((sk_A) != (sk_B))
% 0.19/0.67        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67            = (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.67  thf('4', plain,
% 0.19/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          = (k1_tarski @ sk_A)))
% 0.19/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('split', [status(esa)], ['3'])).
% 0.19/0.67  thf(t83_xboole_1, axiom,
% 0.19/0.67    (![A:$i,B:$i]:
% 0.19/0.67     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.67  thf('5', plain,
% 0.19/0.67      (![X6 : $i, X8 : $i]:
% 0.19/0.67         ((r1_xboole_0 @ X6 @ X8) | ((k4_xboole_0 @ X6 @ X8) != (X6)))),
% 0.19/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.67  thf('6', plain,
% 0.19/0.67      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.19/0.67         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))
% 0.19/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.67  thf('7', plain,
% 0.19/0.67      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.19/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.67  thf(t69_enumset1, axiom,
% 0.19/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.67  thf('8', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.19/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.67  thf(t70_enumset1, axiom,
% 0.19/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.67  thf('9', plain,
% 0.19/0.67      (![X22 : $i, X23 : $i]:
% 0.19/0.67         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.19/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.67  thf(d1_enumset1, axiom,
% 0.19/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.67       ( ![E:$i]:
% 0.19/0.67         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.67           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.67  thf(zf_stmt_2, axiom,
% 0.19/0.67    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.67     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.67       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.67  thf(zf_stmt_3, axiom,
% 0.19/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.67       ( ![E:$i]:
% 0.19/0.67         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.67  thf('10', plain,
% 0.19/0.67      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.67         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.19/0.67          | (r2_hidden @ X14 @ X18)
% 0.19/0.67          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.67  thf('11', plain,
% 0.19/0.67      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.67         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.19/0.67          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.19/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.67  thf('12', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.67         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.67          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.67      inference('sup+', [status(thm)], ['9', '11'])).
% 0.19/0.67  thf('13', plain,
% 0.19/0.67      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.67         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.67  thf('14', plain,
% 0.19/0.67      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.19/0.67      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.67  thf('15', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.67      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.67  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.67      inference('sup+', [status(thm)], ['8', '15'])).
% 0.19/0.67  thf(t3_xboole_0, axiom,
% 0.19/0.67    (![A:$i,B:$i]:
% 0.19/0.67     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.67            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.67  thf('17', plain,
% 0.19/0.67      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.67         (~ (r2_hidden @ X2 @ X0)
% 0.19/0.67          | ~ (r2_hidden @ X2 @ X3)
% 0.19/0.67          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.67  thf('18', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i]:
% 0.19/0.67         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.67  thf('19', plain,
% 0.19/0.67      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.19/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['7', '18'])).
% 0.19/0.67  thf('20', plain,
% 0.19/0.67      ((~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B)))
% 0.19/0.67         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))) & 
% 0.19/0.67             (((sk_A) = (sk_B))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['2', '19'])).
% 0.19/0.67  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.67      inference('sup+', [status(thm)], ['8', '15'])).
% 0.19/0.67  thf('22', plain,
% 0.19/0.67      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.67       ~
% 0.19/0.67       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          = (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.67  thf('23', plain,
% 0.19/0.67      (~ (((sk_A) = (sk_B))) | 
% 0.19/0.67       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          = (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('split', [status(esa)], ['3'])).
% 0.19/0.67  thf('24', plain,
% 0.19/0.67      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.67         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.19/0.67          | ((X10) = (X11))
% 0.19/0.67          | ((X10) = (X12))
% 0.19/0.67          | ((X10) = (X13)))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.67  thf(l27_zfmisc_1, axiom,
% 0.19/0.67    (![A:$i,B:$i]:
% 0.19/0.67     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.19/0.67  thf('25', plain,
% 0.19/0.67      (![X31 : $i, X32 : $i]:
% 0.19/0.67         ((r1_xboole_0 @ (k1_tarski @ X31) @ X32) | (r2_hidden @ X31 @ X32))),
% 0.19/0.67      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.19/0.67  thf('26', plain,
% 0.19/0.67      (![X6 : $i, X7 : $i]:
% 0.19/0.67         (((k4_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.19/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.19/0.67  thf('27', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i]:
% 0.19/0.67         ((r2_hidden @ X1 @ X0)
% 0.19/0.67          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.19/0.67      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.67  thf('28', plain,
% 0.19/0.67      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          != (k1_tarski @ sk_A)))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('split', [status(esa)], ['0'])).
% 0.19/0.67  thf('29', plain,
% 0.19/0.67      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.19/0.67         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.67  thf('30', plain,
% 0.19/0.67      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.67  thf('31', plain,
% 0.19/0.67      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.19/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.67  thf('32', plain,
% 0.19/0.67      (![X22 : $i, X23 : $i]:
% 0.19/0.67         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.19/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.67  thf('33', plain,
% 0.19/0.67      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.67         (~ (r2_hidden @ X19 @ X18)
% 0.19/0.67          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.19/0.67          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.19/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.67  thf('34', plain,
% 0.19/0.67      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.19/0.67         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.19/0.67          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.19/0.67      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.67  thf('35', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.67         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.67          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.67      inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.67  thf('36', plain,
% 0.19/0.67      (![X0 : $i, X1 : $i]:
% 0.19/0.67         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.19/0.67          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.19/0.67      inference('sup-', [status(thm)], ['31', '35'])).
% 0.19/0.67  thf('37', plain,
% 0.19/0.67      ((~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['30', '36'])).
% 0.19/0.67  thf('38', plain,
% 0.19/0.67      (((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B))))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['24', '37'])).
% 0.19/0.67  thf('39', plain,
% 0.19/0.67      ((((sk_A) = (sk_B)))
% 0.19/0.67         <= (~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.67  thf('40', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.19/0.67      inference('split', [status(esa)], ['3'])).
% 0.19/0.67  thf('41', plain,
% 0.19/0.67      ((((sk_B) != (sk_B)))
% 0.19/0.67         <= (~ (((sk_A) = (sk_B))) & 
% 0.19/0.67             ~
% 0.19/0.67             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67                = (k1_tarski @ sk_A))))),
% 0.19/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.67  thf('42', plain,
% 0.19/0.67      ((((sk_A) = (sk_B))) | 
% 0.19/0.67       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.19/0.67          = (k1_tarski @ sk_A)))),
% 0.19/0.67      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.67  thf('43', plain, ($false),
% 0.19/0.67      inference('sat_resolution*', [status(thm)], ['1', '22', '23', '42'])).
% 0.19/0.67  
% 0.19/0.67  % SZS output end Refutation
% 0.19/0.67  
% 0.19/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
