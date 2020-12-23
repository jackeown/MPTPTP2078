%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wuv2lAuLWI

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  90 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   11
%              Number of atoms          :  538 ( 889 expanded)
%              Number of equality atoms :   41 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t64_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( A != C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_zfmisc_1])).

thf('0',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

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

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
    | ( sk_A != sk_C ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
    | ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( X7 = X8 )
      | ( X7 = X9 )
      | ( X7 = X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['11'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X16 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_A = sk_C )
      | ( sk_A = sk_C ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,
    ( ( sk_A = sk_C )
   <= ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) ) )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','23','24','25','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wuv2lAuLWI
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 103 iterations in 0.065s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(t64_zfmisc_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.53        ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.53          ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((((sk_A) != (sk_C))
% 0.22/0.53        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (~ (((sk_A) = (sk_C))) | 
% 0.22/0.53       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf(t76_enumset1, axiom,
% 0.22/0.53    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X18 : $i]: ((k1_enumset1 @ X18 @ X18 @ X18) = (k1_tarski @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.22/0.53  thf(d1_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.53           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.53  thf(zf_stmt_2, axiom,
% 0.22/0.53    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.53     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.53       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_3, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.53       ( ![E:$i]:
% 0.22/0.53         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.22/0.53          | (r2_hidden @ X11 @ X15)
% 0.22/0.53          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.53         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.22/0.53          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.22/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.53          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['2', '4'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.53         (((X7) != (X6)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X6 @ X8 @ X9 @ X6)),
% 0.22/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.53  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((((sk_A) = (sk_C))
% 0.22/0.53        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.22/0.53        | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('10', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ sk_B)
% 0.22/0.53        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))))),
% 0.22/0.53      inference('split', [status(esa)], ['11'])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             (((sk_A) = (sk_C))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['10', '12'])).
% 0.22/0.53  thf(d5_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.53       ( ![D:$i]:
% 0.22/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.53          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             (((sk_A) = (sk_C))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) | 
% 0.22/0.53       ~ (((sk_A) = (sk_C)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['8', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))))),
% 0.22/0.53      inference('split', [status(esa)], ['11'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.53          | (r2_hidden @ X4 @ X1)
% 0.22/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.53         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ sk_B))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('split', [status(esa)], ['9'])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.53       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.53       ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) | 
% 0.22/0.53       (((sk_A) = (sk_C)))),
% 0.22/0.53      inference('split', [status(esa)], ['9'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.53       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['11'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.53         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.22/0.53          | ((X7) = (X8))
% 0.22/0.53          | ((X7) = (X9))
% 0.22/0.53          | ((X7) = (X10)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('split', [status(esa)], ['11'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | (r2_hidden @ X0 @ X3)
% 0.22/0.53          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((r2_hidden @ sk_A @ X0)
% 0.22/0.53           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.22/0.53         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      ((~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C))))
% 0.22/0.53         <= (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))))),
% 0.22/0.53      inference('split', [status(esa)], ['9'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.22/0.53         <= (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X18 : $i]: ((k1_enumset1 @ X18 @ X18 @ X18) = (k1_tarski @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X16 @ X15)
% 0.22/0.53          | ~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.22/0.53          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.22/0.53         (~ (zip_tseitin_0 @ X16 @ X12 @ X13 @ X14)
% 0.22/0.53          | ~ (r2_hidden @ X16 @ (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.53          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['33', '35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      ((~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C))
% 0.22/0.53         <= (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['32', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_C))))
% 0.22/0.53         <= (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['26', '37'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      ((((sk_A) = (sk_C)))
% 0.22/0.53         <= (~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.53  thf('40', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      ((((sk_A) != (sk_A)))
% 0.22/0.53         <= (~ (((sk_A) = (sk_C))) & 
% 0.22/0.53             ~ ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) & 
% 0.22/0.53             ((r2_hidden @ sk_A @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.22/0.53       ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_C)))) | 
% 0.22/0.53       (((sk_A) = (sk_C)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.53  thf('43', plain, ($false),
% 0.22/0.53      inference('sat_resolution*', [status(thm)],
% 0.22/0.53                ['1', '17', '23', '24', '25', '42'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
