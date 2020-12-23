%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nfqnCAKW9N

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:17 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
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
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X63 @ X64 ) )
      = ( k2_xboole_0 @ X63 @ X64 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nfqnCAKW9N
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:42:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.05/2.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.05/2.30  % Solved by: fo/fo7.sh
% 2.05/2.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.30  % done 893 iterations in 1.846s
% 2.05/2.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.05/2.30  % SZS output start Refutation
% 2.05/2.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.05/2.30  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.30  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.30  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.05/2.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.30  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.05/2.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.05/2.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.30  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.05/2.30  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.05/2.30  thf(t47_zfmisc_1, conjecture,
% 2.05/2.30    (![A:$i,B:$i,C:$i]:
% 2.05/2.30     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 2.05/2.30       ( r2_hidden @ A @ C ) ))).
% 2.05/2.30  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.30    (~( ![A:$i,B:$i,C:$i]:
% 2.05/2.30        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 2.05/2.30          ( r2_hidden @ A @ C ) ) )),
% 2.05/2.30    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 2.05/2.30  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 2.05/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.30  thf(t70_enumset1, axiom,
% 2.05/2.30    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.05/2.30  thf('1', plain,
% 2.05/2.30      (![X36 : $i, X37 : $i]:
% 2.05/2.30         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 2.05/2.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.05/2.30  thf(d1_enumset1, axiom,
% 2.05/2.30    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.30     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.05/2.30       ( ![E:$i]:
% 2.05/2.30         ( ( r2_hidden @ E @ D ) <=>
% 2.05/2.30           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.05/2.30  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.05/2.30  thf(zf_stmt_2, axiom,
% 2.05/2.30    (![E:$i,C:$i,B:$i,A:$i]:
% 2.05/2.30     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.05/2.30       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.05/2.30  thf(zf_stmt_3, axiom,
% 2.05/2.30    (![A:$i,B:$i,C:$i,D:$i]:
% 2.05/2.30     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.05/2.30       ( ![E:$i]:
% 2.05/2.30         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.05/2.30  thf('2', plain,
% 2.05/2.30      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.05/2.30         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 2.05/2.30          | (r2_hidden @ X29 @ X33)
% 2.05/2.30          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 2.05/2.30      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.05/2.30  thf('3', plain,
% 2.05/2.30      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.05/2.30         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 2.05/2.30          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 2.05/2.30      inference('simplify', [status(thm)], ['2'])).
% 2.05/2.30  thf('4', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.30         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.05/2.30          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['1', '3'])).
% 2.05/2.30  thf('5', plain,
% 2.05/2.30      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 2.05/2.30         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 2.05/2.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.05/2.30  thf('6', plain,
% 2.05/2.30      (![X24 : $i, X26 : $i, X27 : $i]:
% 2.05/2.30         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 2.05/2.30      inference('simplify', [status(thm)], ['5'])).
% 2.05/2.30  thf('7', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.05/2.30      inference('sup-', [status(thm)], ['4', '6'])).
% 2.05/2.30  thf('8', plain,
% 2.05/2.30      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) @ sk_C_1)),
% 2.05/2.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.30  thf(d10_xboole_0, axiom,
% 2.05/2.30    (![A:$i,B:$i]:
% 2.05/2.30     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.05/2.30  thf('9', plain,
% 2.05/2.30      (![X10 : $i, X12 : $i]:
% 2.05/2.30         (((X10) = (X12))
% 2.05/2.30          | ~ (r1_tarski @ X12 @ X10)
% 2.05/2.30          | ~ (r1_tarski @ X10 @ X12))),
% 2.05/2.30      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.05/2.30  thf('10', plain,
% 2.05/2.30      ((~ (r1_tarski @ sk_C_1 @ 
% 2.05/2.30           (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 2.05/2.30        | ((sk_C_1) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 2.05/2.30      inference('sup-', [status(thm)], ['8', '9'])).
% 2.05/2.30  thf(commutativity_k2_tarski, axiom,
% 2.05/2.30    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.05/2.30  thf('11', plain,
% 2.05/2.30      (![X22 : $i, X23 : $i]:
% 2.05/2.30         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 2.05/2.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.05/2.30  thf(l51_zfmisc_1, axiom,
% 2.05/2.30    (![A:$i,B:$i]:
% 2.05/2.30     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.05/2.30  thf('12', plain,
% 2.05/2.30      (![X63 : $i, X64 : $i]:
% 2.05/2.30         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 2.05/2.30      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.05/2.30  thf('13', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]:
% 2.05/2.30         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['11', '12'])).
% 2.05/2.30  thf('14', plain,
% 2.05/2.30      (![X63 : $i, X64 : $i]:
% 2.05/2.30         ((k3_tarski @ (k2_tarski @ X63 @ X64)) = (k2_xboole_0 @ X63 @ X64))),
% 2.05/2.30      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.05/2.30  thf('15', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['13', '14'])).
% 2.05/2.30  thf(t7_xboole_1, axiom,
% 2.05/2.30    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.05/2.30  thf('16', plain,
% 2.05/2.30      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 2.05/2.30      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.05/2.30  thf('17', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['13', '14'])).
% 2.05/2.30  thf('18', plain,
% 2.05/2.30      (((sk_C_1) = (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 2.05/2.30      inference('demod', [status(thm)], ['10', '15', '16', '17'])).
% 2.05/2.30  thf('19', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.30      inference('sup+', [status(thm)], ['13', '14'])).
% 2.05/2.30  thf('20', plain,
% 2.05/2.30      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 2.05/2.30      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.05/2.30  thf('21', plain,
% 2.05/2.30      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.05/2.30      inference('sup+', [status(thm)], ['19', '20'])).
% 2.05/2.30  thf('22', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 2.05/2.30      inference('sup+', [status(thm)], ['18', '21'])).
% 2.05/2.30  thf(d3_tarski, axiom,
% 2.05/2.30    (![A:$i,B:$i]:
% 2.05/2.30     ( ( r1_tarski @ A @ B ) <=>
% 2.05/2.30       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.05/2.30  thf('23', plain,
% 2.05/2.30      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.05/2.30         (~ (r2_hidden @ X2 @ X3)
% 2.05/2.30          | (r2_hidden @ X2 @ X4)
% 2.05/2.30          | ~ (r1_tarski @ X3 @ X4))),
% 2.05/2.30      inference('cnf', [status(esa)], [d3_tarski])).
% 2.05/2.30  thf('24', plain,
% 2.05/2.30      (![X0 : $i]:
% 2.05/2.30         ((r2_hidden @ X0 @ sk_C_1)
% 2.05/2.30          | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 2.05/2.30      inference('sup-', [status(thm)], ['22', '23'])).
% 2.05/2.30  thf('25', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 2.05/2.30      inference('sup-', [status(thm)], ['7', '24'])).
% 2.05/2.30  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 2.05/2.30  
% 2.05/2.30  % SZS output end Refutation
% 2.05/2.30  
% 2.16/2.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
