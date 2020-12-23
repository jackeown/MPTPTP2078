%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BpkrciVgEI

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  91 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  324 ( 901 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t10_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['2','4'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['2','4'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['18','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BpkrciVgEI
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 50 iterations in 0.052s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.52  thf(t10_mcart_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.52          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.52            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t10_mcart_1])).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.52        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))
% 0.21/0.52         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d2_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ?[E:$i,F:$i]:
% 0.21/0.52             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.52               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_2, axiom,
% 0.21/0.52    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.21/0.52       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.21/0.52         ( r2_hidden @ E @ A ) ) ))).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.21/0.52       ( ![D:$i]:
% 0.21/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.52           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X12 @ X11)
% 0.21/0.52          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.21/0.52             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.21/0.52          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.21/0.52           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.21/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.21/0.52        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((r2_hidden @ X0 @ X4) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('7', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.21/0.52        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         (((X2) = (k4_tarski @ X0 @ X1))
% 0.21/0.52          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((sk_A)
% 0.21/0.52         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.21/0.52            (sk_F_1 @ sk_A @ sk_C @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(t7_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.52       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]: ((k1_mcart_1 @ (k4_tarski @ X16 @ X17)) = (X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('12', plain, (((k1_mcart_1 @ sk_A) = (sk_E_1 @ sk_A @ sk_C @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('13', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '12'])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.21/0.52         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('15', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)) | 
% 0.21/0.52       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.21/0.52      inference('split', [status(esa)], ['0'])).
% 0.21/0.52  thf('17', plain, (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain, (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.21/0.52        (sk_E_1 @ sk_A @ sk_C @ sk_B) @ sk_A @ sk_C @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.52         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.52  thf('21', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_C @ sk_B) @ sk_C)),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((sk_A)
% 0.21/0.52         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_C @ sk_B) @ 
% 0.21/0.52            (sk_F_1 @ sk_A @ sk_C @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('23', plain, (((k1_mcart_1 @ sk_A) = (sk_E_1 @ sk_A @ sk_C @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((sk_A)
% 0.21/0.52         = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_F_1 @ sk_A @ sk_C @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('26', plain, (((k2_mcart_1 @ sk_A) = (sk_F_1 @ sk_A @ sk_C @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '26'])).
% 0.21/0.52  thf('28', plain, ($false), inference('demod', [status(thm)], ['18', '27'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
