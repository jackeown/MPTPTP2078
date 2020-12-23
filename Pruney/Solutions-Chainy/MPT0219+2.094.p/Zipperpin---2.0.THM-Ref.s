%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVTHpYd8h9

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  365 ( 618 expanded)
%              Number of equality atoms :   46 (  81 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B_1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B_1 )
      = ( k2_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ sk_A ) )
      | ( zip_tseitin_0 @ X1 @ sk_B_1 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X20 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B_1 @ ( k2_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B_1 )
      = ( k2_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('17',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_tarski @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X32 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ ( k2_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_A )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_tarski @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_A )
      = ( k2_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ sk_A ) )
      | ~ ( zip_tseitin_0 @ X1 @ sk_A @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ( sk_B_1 = sk_A )
      | ( sk_B_1 = sk_A ) ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = sk_A )
      | ( sk_B_1 = X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] : ( sk_B_1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZVTHpYd8h9
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 153 iterations in 0.055s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(t13_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51         ( k1_tarski @ A ) ) =>
% 0.20/0.51       ( ( A ) = ( B ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.51            ( k1_tarski @ A ) ) =>
% 0.20/0.51          ( ( A ) = ( B ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.20/0.51  thf('0', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d1_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, axiom,
% 0.20/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.20/0.51          | ((X19) = (X20))
% 0.20/0.51          | ((X19) = (X21))
% 0.20/0.51          | ((X19) = (X22)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.20/0.51         = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t41_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k2_tarski @ A @ B ) =
% 0.20/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         ((k2_tarski @ X30 @ X31)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('4', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t42_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X0 @ sk_A @ sk_B_1)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         ((k2_tarski @ X30 @ X31)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X0 @ sk_A @ sk_B_1) = (k2_tarski @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.20/0.51          | (r2_hidden @ X23 @ X27)
% 0.20/0.51          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.20/0.51          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ (k2_tarski @ X0 @ sk_A))
% 0.20/0.51          | (zip_tseitin_0 @ X1 @ sk_B_1 @ sk_A @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['8', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         (((X19) != (X20)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         ~ (zip_tseitin_0 @ X20 @ X20 @ X21 @ X18)),
% 0.20/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i]: (r2_hidden @ sk_B_1 @ (k2_tarski @ X0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X41 : $i, X42 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X0 @ sk_A @ sk_B_1) = (k2_tarski @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('17', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k2_tarski @ sk_A @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('19', plain, (((k1_tarski @ sk_A) = (k2_tarski @ sk_A @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X32 @ X33 @ X34)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X32) @ (k2_tarski @ X33 @ X34)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X0 @ sk_A @ sk_A)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         ((k2_tarski @ X30 @ X31)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X31)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ sk_A @ sk_A) = (k2_tarski @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X28 @ X27)
% 0.20/0.51          | ~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.20/0.51          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.20/0.51         (~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.20/0.51          | ~ (r2_hidden @ X28 @ (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ sk_A))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X1 @ sk_A @ sk_A @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.51  thf('27', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ sk_B_1 @ sk_A @ sk_A @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B_1) = (X0)) | ((sk_B_1) = (sk_A)) | ((sk_B_1) = (sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '27'])).
% 0.20/0.51  thf('29', plain, (![X0 : $i]: (((sk_B_1) = (sk_A)) | ((sk_B_1) = (X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.51  thf('30', plain, (((sk_A) != (sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('31', plain, (![X0 : $i]: ((sk_B_1) = (X0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, (((sk_B_1) != (sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '31'])).
% 0.20/0.51  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
