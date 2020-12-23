%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szHDmofdSB

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:48 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   66 (  77 expanded)
%              Number of leaves         :   30 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  397 ( 482 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X41 ) @ X42 )
      | ( r2_hidden @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( sk_B_1
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_tarski @ X18 @ X17 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','8','9','10'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference('sup-',[status(thm)],['22','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.szHDmofdSB
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 373 iterations in 0.147s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(l27_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (![X41 : $i, X42 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ (k1_tarski @ X41) @ X42) | (r2_hidden @ X41 @ X42))),
% 0.41/0.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.41/0.60  thf(t45_zfmisc_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.41/0.60       ( r2_hidden @ A @ B ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i]:
% 0.41/0.60        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.41/0.60          ( r2_hidden @ A @ B ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d10_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X8 : $i, X10 : $i]:
% 0.41/0.60         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.41/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      ((~ (r1_tarski @ sk_B_1 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.41/0.60        | ((sk_B_1) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.60  thf(commutativity_k2_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X17 : $i, X18 : $i]:
% 0.41/0.60         ((k2_tarski @ X18 @ X17) = (k2_tarski @ X17 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.60  thf(l51_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X43 : $i, X44 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X43 : $i, X44 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf(t7_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['6', '7'])).
% 0.41/0.60  thf('11', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('demod', [status(thm)], ['3', '8', '9', '10'])).
% 0.41/0.60  thf(t70_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.41/0.60            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.41/0.60       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.41/0.60            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.41/0.60         ((r1_xboole_0 @ X11 @ X14)
% 0.41/0.60          | ~ (r1_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X14)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 0.41/0.60          | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['0', '13'])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.41/0.60  thf('16', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.41/0.60  thf(t4_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.41/0.60          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.41/0.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (((r2_hidden @ sk_A @ sk_B_1) | (v1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '19'])).
% 0.41/0.60  thf('21', plain, (~ (r2_hidden @ sk_A @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('22', plain, ((v1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['20', '21'])).
% 0.41/0.60  thf(t69_enumset1, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.60  thf(t70_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.60  thf('24', plain,
% 0.41/0.60      (![X32 : $i, X33 : $i]:
% 0.41/0.60         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.41/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.60  thf(d1_enumset1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.60       ( ![E:$i]:
% 0.41/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.41/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_2, axiom,
% 0.41/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.41/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.41/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_3, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.60       ( ![E:$i]:
% 0.41/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.60         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.41/0.60          | (r2_hidden @ X24 @ X28)
% 0.41/0.60          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.60         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.41/0.60          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.41/0.60      inference('simplify', [status(thm)], ['25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.60          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['24', '26'])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.41/0.60         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 0.41/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '29'])).
% 0.41/0.60  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['23', '30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('33', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.60  thf('34', plain, ($false), inference('sup-', [status(thm)], ['22', '33'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
