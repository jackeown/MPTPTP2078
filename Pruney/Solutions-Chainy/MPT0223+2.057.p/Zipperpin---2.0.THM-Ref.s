%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vagClYj9lr

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:38 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  446 ( 664 expanded)
%              Number of equality atoms :   42 (  61 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['29','40'])).

thf('42',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vagClYj9lr
% 0.11/0.33  % Computer   : n014.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:59:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 304 iterations in 0.132s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(t70_enumset1, axiom,
% 0.35/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.35/0.57  thf('0', plain,
% 0.35/0.57      (![X28 : $i, X29 : $i]:
% 0.35/0.57         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.35/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.57  thf(d1_enumset1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.57       ( ![E:$i]:
% 0.35/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.35/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_1, axiom,
% 0.35/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.35/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.35/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.35/0.57       ( ![E:$i]:
% 0.35/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.35/0.57          | (r2_hidden @ X20 @ X24)
% 0.35/0.57          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.57         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.35/0.57          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.35/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.35/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.35/0.57      inference('sup+', [status(thm)], ['0', '2'])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.57         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.35/0.57         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.35/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.35/0.57          | ((X16) = (X17))
% 0.35/0.57          | ((X16) = (X18))
% 0.35/0.57          | ((X16) = (X19)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf(l27_zfmisc_1, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      (![X33 : $i, X34 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 0.35/0.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.35/0.57  thf(d7_xboole_0, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.35/0.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.57  thf('9', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.57  thf('10', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((r2_hidden @ X1 @ X0)
% 0.35/0.57          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.57  thf(t18_zfmisc_1, conjecture,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.57         ( k1_tarski @ A ) ) =>
% 0.35/0.57       ( ( A ) = ( B ) ) ))).
% 0.35/0.57  thf(zf_stmt_3, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i]:
% 0.35/0.57        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.57            ( k1_tarski @ A ) ) =>
% 0.35/0.57          ( ( A ) = ( B ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.57         = (k1_tarski @ sk_A))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.35/0.57        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.57      inference('sup+', [status(thm)], ['10', '11'])).
% 0.35/0.57  thf(t69_enumset1, axiom,
% 0.35/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.35/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      (![X28 : $i, X29 : $i]:
% 0.35/0.57         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.35/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X25 @ X24)
% 0.35/0.57          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.35/0.57          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.35/0.57          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['14', '16'])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['13', '17'])).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.35/0.57        | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.35/0.57      inference('sup-', [status(thm)], ['12', '18'])).
% 0.35/0.57  thf('20', plain,
% 0.35/0.57      ((((sk_A) = (sk_B))
% 0.35/0.57        | ((sk_A) = (sk_B))
% 0.35/0.57        | ((sk_A) = (sk_B))
% 0.35/0.57        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['7', '19'])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['20'])).
% 0.35/0.57  thf('22', plain, (((sk_A) != (sk_B))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('23', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.35/0.57  thf('24', plain,
% 0.35/0.57      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.35/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.57  thf('25', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.35/0.57  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['24', '25'])).
% 0.35/0.57  thf(t3_xboole_0, axiom,
% 0.35/0.57    (![A:$i,B:$i]:
% 0.35/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.35/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.35/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.35/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.35/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.35/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.57  thf('29', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['23', '28'])).
% 0.35/0.57  thf(idempotence_k3_xboole_0, axiom,
% 0.35/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.35/0.57  thf('30', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.35/0.57      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      (![X0 : $i, X2 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.35/0.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.35/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.57  thf('33', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.35/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.35/0.57  thf('34', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.57  thf('35', plain,
% 0.35/0.57      (![X4 : $i, X5 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.57  thf('36', plain,
% 0.35/0.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X6 @ X4)
% 0.35/0.57          | ~ (r2_hidden @ X6 @ X7)
% 0.35/0.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.35/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.35/0.57  thf('37', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.35/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.35/0.57          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.35/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.57  thf('38', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.35/0.57          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.35/0.57          | (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.35/0.57  thf('39', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i]:
% 0.35/0.57         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.57      inference('simplify', [status(thm)], ['38'])).
% 0.35/0.57  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.35/0.57      inference('sup-', [status(thm)], ['33', '39'])).
% 0.35/0.57  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.35/0.57      inference('demod', [status(thm)], ['29', '40'])).
% 0.35/0.57  thf('42', plain, ($false), inference('sup-', [status(thm)], ['6', '41'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
