%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hIEZhzqc3z

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:17 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  306 ( 447 expanded)
%              Number of equality atoms :   25 (  40 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('18',plain,
    ( sk_C_1
    = ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['18','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hIEZhzqc3z
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:05:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.74/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/0.94  % Solved by: fo/fo7.sh
% 0.74/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.94  % done 703 iterations in 0.463s
% 0.74/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/0.94  % SZS output start Refutation
% 0.74/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.74/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.94  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.74/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.74/0.94  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.74/0.94  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.74/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.94  thf(t47_zfmisc_1, conjecture,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.74/0.94       ( r2_hidden @ A @ C ) ))).
% 0.74/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.94    (~( ![A:$i,B:$i,C:$i]:
% 0.74/0.94        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.74/0.94          ( r2_hidden @ A @ C ) ) )),
% 0.74/0.94    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.74/0.94  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(t70_enumset1, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.74/0.94  thf('1', plain,
% 0.74/0.94      (![X41 : $i, X42 : $i]:
% 0.74/0.94         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.74/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.74/0.94  thf(d1_enumset1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.74/0.94       ( ![E:$i]:
% 0.74/0.94         ( ( r2_hidden @ E @ D ) <=>
% 0.74/0.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.74/0.94  thf(zf_stmt_2, axiom,
% 0.74/0.94    (![E:$i,C:$i,B:$i,A:$i]:
% 0.74/0.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.74/0.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_3, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.74/0.94       ( ![E:$i]:
% 0.74/0.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.74/0.94  thf('2', plain,
% 0.74/0.94      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.74/0.94         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 0.74/0.94          | (r2_hidden @ X34 @ X38)
% 0.74/0.94          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.74/0.94  thf('3', plain,
% 0.74/0.94      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.74/0.94         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 0.74/0.94          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 0.74/0.94      inference('simplify', [status(thm)], ['2'])).
% 0.74/0.94  thf('4', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.74/0.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['1', '3'])).
% 0.74/0.94  thf('5', plain,
% 0.74/0.94      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.74/0.94         (((X30) != (X29)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.94  thf('6', plain,
% 0.74/0.94      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.74/0.94         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X29)),
% 0.74/0.94      inference('simplify', [status(thm)], ['5'])).
% 0.74/0.94  thf('7', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.74/0.94      inference('sup-', [status(thm)], ['4', '6'])).
% 0.74/0.94  thf('8', plain,
% 0.74/0.94      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(d10_xboole_0, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.74/0.94  thf('9', plain,
% 0.74/0.94      (![X7 : $i, X9 : $i]:
% 0.74/0.94         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.74/0.94  thf('10', plain,
% 0.74/0.94      ((~ (r1_tarski @ sk_C_1 @ 
% 0.74/0.94           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.74/0.94        | ((sk_C_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.94  thf(commutativity_k2_tarski, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.74/0.94  thf('11', plain,
% 0.74/0.94      (![X27 : $i, X28 : $i]:
% 0.74/0.94         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.74/0.94      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.74/0.94  thf(l51_zfmisc_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('12', plain,
% 0.74/0.94      (![X68 : $i, X69 : $i]:
% 0.74/0.94         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.74/0.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.74/0.94  thf('13', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['11', '12'])).
% 0.74/0.94  thf('14', plain,
% 0.74/0.94      (![X68 : $i, X69 : $i]:
% 0.74/0.94         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.74/0.94      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.74/0.94  thf('15', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.94  thf(t7_xboole_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.74/0.94  thf('16', plain,
% 0.74/0.94      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.74/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.74/0.94  thf('17', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.94  thf('18', plain,
% 0.74/0.94      (((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.74/0.94      inference('demod', [status(thm)], ['10', '15', '16', '17'])).
% 0.74/0.94  thf('19', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.74/0.94      inference('sup+', [status(thm)], ['13', '14'])).
% 0.74/0.94  thf('20', plain,
% 0.74/0.94      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.74/0.94      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.74/0.94  thf('21', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['19', '20'])).
% 0.74/0.94  thf('22', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.74/0.94      inference('sup+', [status(thm)], ['18', '21'])).
% 0.74/0.94  thf(d3_tarski, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( r1_tarski @ A @ B ) <=>
% 0.74/0.94       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.74/0.94  thf('23', plain,
% 0.74/0.94      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.94         (~ (r2_hidden @ X2 @ X3)
% 0.74/0.94          | (r2_hidden @ X2 @ X4)
% 0.74/0.94          | ~ (r1_tarski @ X3 @ X4))),
% 0.74/0.94      inference('cnf', [status(esa)], [d3_tarski])).
% 0.74/0.94  thf('24', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((r2_hidden @ X0 @ sk_C_1)
% 0.74/0.94          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/0.94  thf('25', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.74/0.94      inference('sup-', [status(thm)], ['7', '24'])).
% 0.74/0.94  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.74/0.94  
% 0.74/0.94  % SZS output end Refutation
% 0.74/0.94  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
