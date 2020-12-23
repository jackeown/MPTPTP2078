%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K1EZJkiCsd

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:57 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   44 (  84 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  325 ( 843 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','6'])).

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

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X17 @ X18 ) @ ( sk_E_1 @ X20 @ X17 @ X18 ) @ X20 @ X17 @ X18 )
      | ( X19
       != ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X17 @ X18 ) @ ( sk_E_1 @ X20 @ X17 @ X18 ) @ X20 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
        = ( k4_tarski @ X8 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,
    ( sk_D_2
    = ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X8 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ( sk_D_2
       != ( k4_tarski @ X24 @ X25 ) )
      | ~ ( r2_hidden @ X25 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( sk_D_2
       != ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_D_2 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['7','9'])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_D_2 != sk_D_2 ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.K1EZJkiCsd
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 174 iterations in 0.096s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.37/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.37/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.55  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.37/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.55  thf(t103_zfmisc_1, conjecture,
% 0.37/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.37/0.55          ( r2_hidden @ D @ A ) & 
% 0.37/0.55          ( ![E:$i,F:$i]:
% 0.37/0.55            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.37/0.55                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.55        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.37/0.55             ( r2_hidden @ D @ A ) & 
% 0.37/0.55             ( ![E:$i,F:$i]:
% 0.37/0.55               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.37/0.55                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 0.37/0.55  thf('0', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('1', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf(t28_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.55  thf('2', plain,
% 0.37/0.55      (![X6 : $i, X7 : $i]:
% 0.37/0.55         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.55  thf('3', plain,
% 0.37/0.55      (((k3_xboole_0 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)) = (sk_A))),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.55  thf(d4_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.55          | (r2_hidden @ X4 @ X2)
% 0.37/0.55          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.55         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['4'])).
% 0.37/0.55  thf('6', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.55          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['3', '5'])).
% 0.37/0.55  thf('7', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['0', '6'])).
% 0.37/0.55  thf(d2_zfmisc_1, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ?[E:$i,F:$i]:
% 0.37/0.55             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.37/0.55               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.37/0.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.37/0.55  thf(zf_stmt_2, axiom,
% 0.37/0.55    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.37/0.55     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.37/0.55       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.37/0.55         ( r2_hidden @ E @ A ) ) ))).
% 0.37/0.55  thf(zf_stmt_3, axiom,
% 0.37/0.55    (![A:$i,B:$i,C:$i]:
% 0.37/0.55     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.37/0.55       ( ![D:$i]:
% 0.37/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.55           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X20 @ X19)
% 0.37/0.55          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X17 @ X18) @ 
% 0.37/0.55             (sk_E_1 @ X20 @ X17 @ X18) @ X20 @ X17 @ X18)
% 0.37/0.55          | ((X19) != (k2_zfmisc_1 @ X18 @ X17)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.37/0.55         ((zip_tseitin_0 @ (sk_F_1 @ X20 @ X17 @ X18) @ 
% 0.37/0.55           (sk_E_1 @ X20 @ X17 @ X18) @ X20 @ X17 @ X18)
% 0.37/0.55          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X18 @ X17)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.37/0.55        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         (((X10) = (k4_tarski @ X8 @ X9))
% 0.37/0.55          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (((sk_D_2)
% 0.37/0.55         = (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.37/0.55            (sk_F_1 @ sk_D_2 @ sk_C @ sk_B)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.55  thf('13', plain,
% 0.37/0.55      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.37/0.55        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         ((r2_hidden @ X8 @ X12)
% 0.37/0.55          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.55  thf('15', plain, ((r2_hidden @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X24 : $i, X25 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X24 @ sk_B)
% 0.37/0.55          | ((sk_D_2) != (k4_tarski @ X24 @ X25))
% 0.37/0.55          | ~ (r2_hidden @ X25 @ sk_C))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X0 @ sk_C)
% 0.37/0.55          | ((sk_D_2) != (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      ((((sk_D_2) != (sk_D_2))
% 0.37/0.55        | ~ (r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_C))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ 
% 0.37/0.55        (sk_E_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_D_2 @ sk_C @ sk_B)),
% 0.37/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.55         ((r2_hidden @ X9 @ X11)
% 0.37/0.55          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.55  thf('21', plain, ((r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C @ sk_B) @ sk_C)),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.55  thf('22', plain, (((sk_D_2) != (sk_D_2))),
% 0.37/0.55      inference('demod', [status(thm)], ['18', '21'])).
% 0.37/0.55  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
