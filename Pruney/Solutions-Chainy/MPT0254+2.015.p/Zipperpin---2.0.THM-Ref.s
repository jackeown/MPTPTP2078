%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gKxov0CeLO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:38 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   48 (  49 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  248 ( 253 expanded)
%              Number of equality atoms :   24 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
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

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gKxov0CeLO
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.73/1.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.73/1.93  % Solved by: fo/fo7.sh
% 1.73/1.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.93  % done 2422 iterations in 1.462s
% 1.73/1.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.73/1.93  % SZS output start Refutation
% 1.73/1.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.73/1.93  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.73/1.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.73/1.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.73/1.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.73/1.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.73/1.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.73/1.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.73/1.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.73/1.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.73/1.93  thf(t49_zfmisc_1, conjecture,
% 1.73/1.93    (![A:$i,B:$i]:
% 1.73/1.93     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 1.73/1.93  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.93    (~( ![A:$i,B:$i]:
% 1.73/1.93        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 1.73/1.93    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 1.73/1.93  thf('0', plain,
% 1.73/1.93      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 1.73/1.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.93  thf(t7_xboole_1, axiom,
% 1.73/1.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.73/1.93  thf('1', plain,
% 1.73/1.93      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.73/1.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.73/1.93  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 1.73/1.93      inference('sup+', [status(thm)], ['0', '1'])).
% 1.73/1.93  thf(t28_xboole_1, axiom,
% 1.73/1.93    (![A:$i,B:$i]:
% 1.73/1.93     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.73/1.93  thf('3', plain,
% 1.73/1.93      (![X14 : $i, X15 : $i]:
% 1.73/1.93         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.73/1.93      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.73/1.93  thf('4', plain,
% 1.73/1.93      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 1.73/1.93      inference('sup-', [status(thm)], ['2', '3'])).
% 1.73/1.93  thf(t2_boole, axiom,
% 1.73/1.93    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.73/1.93  thf('5', plain,
% 1.73/1.93      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.93      inference('cnf', [status(esa)], [t2_boole])).
% 1.73/1.93  thf('6', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 1.73/1.93      inference('demod', [status(thm)], ['4', '5'])).
% 1.73/1.93  thf(t69_enumset1, axiom,
% 1.73/1.93    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.73/1.93  thf('7', plain, (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 1.73/1.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.73/1.93  thf(t70_enumset1, axiom,
% 1.73/1.93    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.73/1.93  thf('8', plain,
% 1.73/1.93      (![X42 : $i, X43 : $i]:
% 1.73/1.93         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 1.73/1.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.73/1.93  thf(d1_enumset1, axiom,
% 1.73/1.93    (![A:$i,B:$i,C:$i,D:$i]:
% 1.73/1.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.73/1.93       ( ![E:$i]:
% 1.73/1.93         ( ( r2_hidden @ E @ D ) <=>
% 1.73/1.93           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.73/1.93  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.73/1.93  thf(zf_stmt_2, axiom,
% 1.73/1.93    (![E:$i,C:$i,B:$i,A:$i]:
% 1.73/1.93     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.73/1.93       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.73/1.93  thf(zf_stmt_3, axiom,
% 1.73/1.93    (![A:$i,B:$i,C:$i,D:$i]:
% 1.73/1.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.73/1.93       ( ![E:$i]:
% 1.73/1.93         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.73/1.93  thf('9', plain,
% 1.73/1.93      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.73/1.93         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 1.73/1.93          | (r2_hidden @ X34 @ X38)
% 1.73/1.93          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 1.73/1.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.73/1.93  thf('10', plain,
% 1.73/1.93      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.73/1.93         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 1.73/1.93          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 1.73/1.93      inference('simplify', [status(thm)], ['9'])).
% 1.73/1.93  thf('11', plain,
% 1.73/1.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.93         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.73/1.93          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.73/1.93      inference('sup+', [status(thm)], ['8', '10'])).
% 1.73/1.93  thf('12', plain,
% 1.73/1.93      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.73/1.93         (((X30) != (X29)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 1.73/1.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.73/1.93  thf('13', plain,
% 1.73/1.93      (![X29 : $i, X31 : $i, X32 : $i]:
% 1.73/1.93         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X29)),
% 1.73/1.93      inference('simplify', [status(thm)], ['12'])).
% 1.73/1.93  thf('14', plain,
% 1.73/1.93      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.73/1.93      inference('sup-', [status(thm)], ['11', '13'])).
% 1.73/1.93  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.73/1.93      inference('sup+', [status(thm)], ['7', '14'])).
% 1.73/1.93  thf('16', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 1.73/1.93      inference('sup+', [status(thm)], ['6', '15'])).
% 1.73/1.93  thf('17', plain,
% 1.73/1.93      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.93      inference('cnf', [status(esa)], [t2_boole])).
% 1.73/1.93  thf(t4_xboole_0, axiom,
% 1.73/1.93    (![A:$i,B:$i]:
% 1.73/1.93     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.73/1.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.73/1.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.73/1.93            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.73/1.93  thf('18', plain,
% 1.73/1.93      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.73/1.93         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.73/1.93          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.73/1.93      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.73/1.93  thf('19', plain,
% 1.73/1.93      (![X0 : $i, X1 : $i]:
% 1.73/1.93         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.73/1.93      inference('sup-', [status(thm)], ['17', '18'])).
% 1.73/1.93  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.73/1.93  thf('20', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.73/1.93      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.73/1.93  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.73/1.93      inference('demod', [status(thm)], ['19', '20'])).
% 1.73/1.93  thf('22', plain, ($false), inference('sup-', [status(thm)], ['16', '21'])).
% 1.73/1.93  
% 1.73/1.93  % SZS output end Refutation
% 1.73/1.93  
% 1.73/1.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
