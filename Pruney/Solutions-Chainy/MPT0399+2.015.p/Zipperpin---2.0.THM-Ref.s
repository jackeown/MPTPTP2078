%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5kEdaVJbGM

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  80 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  292 ( 405 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('0',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X13 @ X9 @ X10 ) @ ( sk_E @ X13 @ X9 @ X10 ) @ ( sk_D @ X13 @ X9 @ X10 ) @ X9 @ X10 )
      | ( r2_hidden @ ( sk_D @ X13 @ X9 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_zfmisc_1 @ X17 @ X18 )
        = k1_xboole_0 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k2_zfmisc_1 @ X17 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ o_0_0_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( o_0_0_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    r1_setfam_1 @ sk_A @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X21 @ X22 ) @ X22 )
      | ~ ( r2_hidden @ X21 @ X23 )
      | ~ ( r1_setfam_1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ o_0_0_xboole_0 ) @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k2_zfmisc_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = o_0_0_xboole_0 )
      | ( X17 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X17 @ X16 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_A = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('30',plain,(
    ! [X0: $i] : ( X0 = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5kEdaVJbGM
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 40 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.48  thf(t21_setfam_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.21/0.48  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.21/0.48  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.48  thf('2', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf(d2_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ?[E:$i,F:$i]:
% 0.21/0.48             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.48               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.48  thf(zf_stmt_2, axiom,
% 0.21/0.48    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.48     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.48       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.48         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.48  thf(zf_stmt_3, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.21/0.48         (((X13) = (k2_zfmisc_1 @ X10 @ X9))
% 0.21/0.48          | (zip_tseitin_0 @ (sk_F @ X13 @ X9 @ X10) @ 
% 0.21/0.48             (sk_E @ X13 @ X9 @ X10) @ (sk_D @ X13 @ X9 @ X10) @ X9 @ X10)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X13 @ X9 @ X10) @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.48          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.21/0.48          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf(t113_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (((k2_zfmisc_1 @ X17 @ X18) = (k1_xboole_0))
% 0.21/0.48          | ((X18) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X17 : $i]: ((k2_zfmisc_1 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.48  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X17 : $i]: ((k2_zfmisc_1 @ X17 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.48  thf(t152_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X19 : $i, X20 : $i]: ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.21/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.21/0.48  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_F @ o_0_0_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.48          | ((o_0_0_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '12'])).
% 0.21/0.48  thf('14', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.48  thf('16', plain, ((r1_setfam_1 @ sk_A @ o_0_0_xboole_0)),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf(d2_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ~( ( r2_hidden @ C @ A ) & 
% 0.21/0.48              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_D_1 @ X21 @ X22) @ X22)
% 0.21/0.49          | ~ (r2_hidden @ X21 @ X23)
% 0.21/0.49          | ~ (r1_setfam_1 @ X23 @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.49          | (r2_hidden @ (sk_D_1 @ X0 @ o_0_0_xboole_0) @ o_0_0_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]: ((o_0_0_xboole_0) = (k2_zfmisc_1 @ X0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ((X17) = (k1_xboole_0))
% 0.21/0.49          | ((k2_zfmisc_1 @ X17 @ X16) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.49  thf('23', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.49  thf('24', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.49  thf('25', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (((X16) = (o_0_0_xboole_0))
% 0.21/0.49          | ((X17) = (o_0_0_xboole_0))
% 0.21/0.49          | ((k2_zfmisc_1 @ X17 @ X16) != (o_0_0_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.21/0.49          | ((X0) = (o_0_0_xboole_0))
% 0.21/0.49          | ((sk_A) = (o_0_0_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i]: (((sk_A) = (o_0_0_xboole_0)) | ((X0) = (o_0_0_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.49  thf('29', plain, (((sk_A) != (o_0_0_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('30', plain, (![X0 : $i]: ((X0) = (o_0_0_xboole_0))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '30'])).
% 0.21/0.49  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
