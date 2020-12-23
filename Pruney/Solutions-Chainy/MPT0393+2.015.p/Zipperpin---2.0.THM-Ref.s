%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QFO3aLKVqN

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  483 ( 939 expanded)
%              Number of equality atoms :   56 ( 109 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X42 @ X41 ) @ X41 )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ~ ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X34 ) )
      = X34 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('7',plain,(
    ! [X37: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X37 ) @ ( k3_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

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

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r1_tarski @ X42 @ ( sk_C_1 @ X42 @ X41 ) )
      | ( r1_tarski @ X42 @ ( k1_setfam_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ~ ( r1_tarski @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( r2_hidden @ X18 @ X22 )
      | ( X22
       != ( k1_enumset1 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t5_setfam_1,axiom,(
    ! [A: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ A )
     => ( ( k1_setfam_1 @ A )
        = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X40: $i] :
      ( ( ( k1_setfam_1 @ X40 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t5_setfam_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2 )
      | ( ( k1_setfam_1 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X15 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X0 @ X1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ ( k1_enumset1 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ ( k1_setfam_1 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ k1_xboole_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X14 != X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('39',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X15 @ X16 @ X13 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['26','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['23','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QFO3aLKVqN
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.93  % Solved by: fo/fo7.sh
% 0.68/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.93  % done 705 iterations in 0.472s
% 0.68/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.93  % SZS output start Refutation
% 0.68/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.68/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.93  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.68/0.93  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.68/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.93  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.93  thf(t11_setfam_1, conjecture,
% 0.68/0.93    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.68/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.93    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.68/0.93    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.68/0.93  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf(t6_setfam_1, axiom,
% 0.68/0.93    (![A:$i,B:$i]:
% 0.68/0.93     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.68/0.93       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.68/0.93  thf('1', plain,
% 0.68/0.93      (![X41 : $i, X42 : $i]:
% 0.68/0.93         (((X41) = (k1_xboole_0))
% 0.68/0.93          | (r2_hidden @ (sk_C_1 @ X42 @ X41) @ X41)
% 0.68/0.93          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.68/0.93      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.68/0.93  thf(l1_zfmisc_1, axiom,
% 0.68/0.93    (![A:$i,B:$i]:
% 0.68/0.93     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.68/0.93  thf('2', plain,
% 0.68/0.93      (![X31 : $i, X33 : $i]:
% 0.68/0.93         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 0.68/0.93      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.93  thf('3', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i]:
% 0.68/0.93         ((r1_tarski @ X1 @ (k1_setfam_1 @ X0))
% 0.68/0.93          | ((X0) = (k1_xboole_0))
% 0.68/0.93          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X1 @ X0)) @ X0))),
% 0.68/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.93  thf(t6_zfmisc_1, axiom,
% 0.68/0.93    (![A:$i,B:$i]:
% 0.68/0.93     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.68/0.93       ( ( A ) = ( B ) ) ))).
% 0.68/0.93  thf('4', plain,
% 0.68/0.93      (![X35 : $i, X36 : $i]:
% 0.68/0.93         (((X36) = (X35))
% 0.68/0.93          | ~ (r1_tarski @ (k1_tarski @ X36) @ (k1_tarski @ X35)))),
% 0.68/0.93      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.68/0.93  thf('5', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i]:
% 0.68/0.93         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.93          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['3', '4'])).
% 0.68/0.93  thf(t31_zfmisc_1, axiom,
% 0.68/0.93    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.68/0.93  thf('6', plain, (![X34 : $i]: ((k3_tarski @ (k1_tarski @ X34)) = (X34))),
% 0.68/0.93      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.68/0.93  thf(t3_setfam_1, axiom,
% 0.68/0.93    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.68/0.93  thf('7', plain,
% 0.68/0.93      (![X37 : $i]: (r1_tarski @ (k1_setfam_1 @ X37) @ (k3_tarski @ X37))),
% 0.68/0.93      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.68/0.93  thf('8', plain,
% 0.68/0.93      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.68/0.93      inference('sup+', [status(thm)], ['6', '7'])).
% 0.68/0.93  thf(d10_xboole_0, axiom,
% 0.68/0.93    (![A:$i,B:$i]:
% 0.68/0.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.93  thf('9', plain,
% 0.68/0.93      (![X10 : $i, X12 : $i]:
% 0.68/0.93         (((X10) = (X12))
% 0.68/0.93          | ~ (r1_tarski @ X12 @ X10)
% 0.68/0.93          | ~ (r1_tarski @ X10 @ X12))),
% 0.68/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.93  thf('10', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.93  thf('11', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (((sk_C_1 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.93          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['5', '10'])).
% 0.68/0.93  thf('12', plain,
% 0.68/0.93      (![X41 : $i, X42 : $i]:
% 0.68/0.93         (((X41) = (k1_xboole_0))
% 0.68/0.93          | ~ (r1_tarski @ X42 @ (sk_C_1 @ X42 @ X41))
% 0.68/0.93          | (r1_tarski @ X42 @ (k1_setfam_1 @ X41)))),
% 0.68/0.93      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.68/0.93  thf('13', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (~ (r1_tarski @ X0 @ X0)
% 0.68/0.93          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.93          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.93  thf('14', plain,
% 0.68/0.93      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.68/0.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.93  thf('15', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.68/0.93      inference('simplify', [status(thm)], ['14'])).
% 0.68/0.93  thf('16', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.93          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.93      inference('demod', [status(thm)], ['13', '15'])).
% 0.68/0.93  thf('17', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.68/0.93          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.93      inference('simplify', [status(thm)], ['16'])).
% 0.68/0.93  thf('18', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.68/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.93  thf('19', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.68/0.93          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.68/0.93      inference('clc', [status(thm)], ['17', '18'])).
% 0.68/0.93  thf('20', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.93  thf('21', plain,
% 0.68/0.93      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.93  thf('22', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.93      inference('simplify', [status(thm)], ['21'])).
% 0.68/0.93  thf('23', plain, (((k1_setfam_1 @ k1_xboole_0) != (sk_A))),
% 0.68/0.93      inference('demod', [status(thm)], ['0', '22'])).
% 0.68/0.93  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.68/0.93      inference('simplify', [status(thm)], ['21'])).
% 0.68/0.93  thf('25', plain,
% 0.68/0.93      (![X35 : $i, X36 : $i]:
% 0.68/0.93         (((X36) = (X35))
% 0.68/0.93          | ~ (r1_tarski @ (k1_tarski @ X36) @ (k1_tarski @ X35)))),
% 0.68/0.93      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.68/0.93  thf('26', plain,
% 0.68/0.93      (![X0 : $i]:
% 0.68/0.93         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.93  thf(d1_enumset1, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.93       ( ![E:$i]:
% 0.68/0.93         ( ( r2_hidden @ E @ D ) <=>
% 0.68/0.93           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.93  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.68/0.93  thf(zf_stmt_2, axiom,
% 0.68/0.93    (![E:$i,C:$i,B:$i,A:$i]:
% 0.68/0.93     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.68/0.93       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.68/0.93  thf(zf_stmt_3, axiom,
% 0.68/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.93       ( ![E:$i]:
% 0.68/0.93         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.68/0.93  thf('27', plain,
% 0.68/0.93      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.93         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.68/0.93          | (r2_hidden @ X18 @ X22)
% 0.68/0.93          | ((X22) != (k1_enumset1 @ X21 @ X20 @ X19)))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.93  thf('28', plain,
% 0.68/0.93      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.93         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.68/0.93          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.68/0.93      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.93  thf(t5_setfam_1, axiom,
% 0.68/0.93    (![A:$i]:
% 0.68/0.93     ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.68/0.93       ( ( k1_setfam_1 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.93  thf('29', plain,
% 0.68/0.93      (![X40 : $i]:
% 0.68/0.93         (((k1_setfam_1 @ X40) = (k1_xboole_0))
% 0.68/0.93          | ~ (r2_hidden @ k1_xboole_0 @ X40))),
% 0.68/0.93      inference('cnf', [status(esa)], [t5_setfam_1])).
% 0.68/0.93  thf('30', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.93         ((zip_tseitin_0 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.68/0.93          | ((k1_setfam_1 @ (k1_enumset1 @ X2 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.68/0.93      inference('sup-', [status(thm)], ['28', '29'])).
% 0.68/0.93  thf('31', plain,
% 0.68/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.93         (((X14) != (X15)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.93  thf('32', plain,
% 0.68/0.93      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.68/0.93         ~ (zip_tseitin_0 @ X15 @ X15 @ X16 @ X13)),
% 0.68/0.93      inference('simplify', [status(thm)], ['31'])).
% 0.68/0.93  thf('33', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i]:
% 0.68/0.93         ((k1_setfam_1 @ (k1_enumset1 @ X0 @ X1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.68/0.93      inference('sup-', [status(thm)], ['30', '32'])).
% 0.68/0.93  thf('34', plain,
% 0.68/0.93      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.93         ((r2_hidden @ X18 @ (k1_enumset1 @ X21 @ X20 @ X19))
% 0.68/0.93          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21))),
% 0.68/0.93      inference('simplify', [status(thm)], ['27'])).
% 0.68/0.93  thf(t4_setfam_1, axiom,
% 0.68/0.93    (![A:$i,B:$i]:
% 0.68/0.93     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.68/0.93  thf('35', plain,
% 0.68/0.93      (![X38 : $i, X39 : $i]:
% 0.68/0.93         ((r1_tarski @ (k1_setfam_1 @ X38) @ X39) | ~ (r2_hidden @ X39 @ X38))),
% 0.68/0.93      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.68/0.93  thf('36', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.93         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 0.68/0.93          | (r1_tarski @ (k1_setfam_1 @ (k1_enumset1 @ X2 @ X1 @ X0)) @ X3))),
% 0.68/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.93  thf('37', plain,
% 0.68/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.93         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.68/0.93          | (zip_tseitin_0 @ X0 @ k1_xboole_0 @ X1 @ X2))),
% 0.68/0.93      inference('sup+', [status(thm)], ['33', '36'])).
% 0.68/0.93  thf('38', plain,
% 0.68/0.93      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.93         (((X14) != (X13)) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.68/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.93  thf('39', plain,
% 0.68/0.93      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.68/0.93         ~ (zip_tseitin_0 @ X13 @ X15 @ X16 @ X13)),
% 0.68/0.93      inference('simplify', [status(thm)], ['38'])).
% 0.68/0.93  thf('40', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.68/0.93      inference('sup-', [status(thm)], ['37', '39'])).
% 0.68/0.93  thf('41', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.68/0.93      inference('demod', [status(thm)], ['26', '40'])).
% 0.68/0.93  thf('42', plain, (((sk_A) != (sk_A))),
% 0.68/0.93      inference('demod', [status(thm)], ['23', '41'])).
% 0.68/0.93  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.68/0.93  
% 0.68/0.93  % SZS output end Refutation
% 0.68/0.93  
% 0.80/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
