%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D6lcdUWRXV

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  90 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  317 ( 840 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t103_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ D @ A )
          & ! [E: $i,F: $i] :
              ~ ( ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C )
                & ( D
                  = ( k4_tarski @ E @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ( X14
       != ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X15 @ X12 @ X13 ) @ ( sk_E_1 @ X15 @ X12 @ X13 ) @ X15 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5
        = ( k4_tarski @ X3 @ X4 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,
    ( sk_D_1
    = ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['8','10'])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X3 @ X7 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( sk_D_1
       != ( k4_tarski @ X22 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( sk_D_1
       != ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['8','10'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ X6 )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_D_1 != sk_D_1 ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D6lcdUWRXV
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 81 iterations in 0.041s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(t103_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.50          ( r2_hidden @ D @ A ) & 
% 0.22/0.50          ( ![E:$i,F:$i]:
% 0.22/0.50            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.50                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.22/0.50             ( r2_hidden @ D @ A ) & 
% 0.22/0.50             ( ![E:$i,F:$i]:
% 0.22/0.50               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.50                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 0.22/0.50  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(l1_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X19 : $i, X21 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X19) @ X21) | ~ (r2_hidden @ X19 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.50  thf('3', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf(t1_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.50       ( r1_tarski @ A @ C ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.50          | (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ sk_D_1) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((r1_tarski @ (k1_tarski @ sk_D_1) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i]:
% 0.22/0.50         ((r2_hidden @ X19 @ X20) | ~ (r1_tarski @ (k1_tarski @ X19) @ X20))),
% 0.22/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.50  thf('8', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf(d2_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ?[E:$i,F:$i]:
% 0.22/0.50             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.22/0.50               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.22/0.50       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.22/0.50         ( r2_hidden @ E @ A ) ) ))).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X15 @ X14)
% 0.22/0.50          | (zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 0.22/0.50             (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 0.22/0.50          | ((X14) != (k2_zfmisc_1 @ X13 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ (sk_F_1 @ X15 @ X12 @ X13) @ 
% 0.22/0.50           (sk_E_1 @ X15 @ X12 @ X13) @ X15 @ X12 @ X13)
% 0.22/0.50          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X13 @ X12)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.22/0.50        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         (((X5) = (k4_tarski @ X3 @ X4))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((sk_D_1)
% 0.22/0.50         = (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.22/0.50            (sk_F_1 @ sk_D_1 @ sk_C @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.22/0.50        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((r2_hidden @ X3 @ X7) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('16', plain, ((r2_hidden @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X22 @ sk_B)
% 0.22/0.50          | ((sk_D_1) != (k4_tarski @ X22 @ X23))
% 0.22/0.50          | ~ (r2_hidden @ X23 @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_C)
% 0.22/0.50          | ((sk_D_1) != (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      ((((sk_D_1) != (sk_D_1))
% 0.22/0.50        | ~ (r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.22/0.50        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((r2_hidden @ X4 @ X6) | ~ (zip_tseitin_0 @ X4 @ X3 @ X5 @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('22', plain, ((r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain, (((sk_D_1) != (sk_D_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '22'])).
% 0.22/0.50  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
