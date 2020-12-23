%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wswtD39YVx

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:30 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   54 (  98 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  382 ( 933 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r2_hidden @ D @ C )
          & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ A )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( D
                   != ( k4_tarski @ E @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_subset_1])).

thf('0',plain,(
    r2_hidden @ sk_D_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = sk_C ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X23 @ X20 @ X21 ) @ ( sk_E_1 @ X23 @ X20 @ X21 ) @ X23 @ X20 @ X21 )
      | ( X22
       != ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X23 @ X20 @ X21 ) @ ( sk_E_1 @ X23 @ X20 @ X21 ) @ X23 @ X20 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13
        = ( k4_tarski @ X11 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,
    ( sk_D_2
    = ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( m1_subset_1 @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B_1 )
      | ( sk_D_2
       != ( k4_tarski @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D_2
       != ( k4_tarski @ X0 @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ~ ( m1_subset_1 @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_D_2 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X11 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ X27 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_D_2 != sk_D_2 ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wswtD39YVx
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:19:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 616 iterations in 0.371s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.62/0.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.62/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.83  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.62/0.83  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.62/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.62/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(t65_subset_1, conjecture,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83     ( ~( ( r2_hidden @ D @ C ) & 
% 0.62/0.83          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.62/0.83          ( ![E:$i]:
% 0.62/0.83            ( ( m1_subset_1 @ E @ A ) =>
% 0.62/0.83              ( ![F:$i]:
% 0.62/0.83                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83        ( ~( ( r2_hidden @ D @ C ) & 
% 0.62/0.83             ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.62/0.83             ( ![E:$i]:
% 0.62/0.83               ( ( m1_subset_1 @ E @ A ) =>
% 0.62/0.83                 ( ![F:$i]:
% 0.62/0.83                   ( ( m1_subset_1 @ F @ B ) =>
% 0.62/0.83                     ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t65_subset_1])).
% 0.62/0.83  thf('0', plain, ((r2_hidden @ sk_D_2 @ sk_C)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('1', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(t28_xboole_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.83  thf('2', plain,
% 0.62/0.83      (![X9 : $i, X10 : $i]:
% 0.62/0.83         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.62/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.83  thf('3', plain,
% 0.62/0.83      (((k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (sk_C))),
% 0.62/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.83  thf(d4_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.62/0.83       ( ![D:$i]:
% 0.62/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.83           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.62/0.83  thf('4', plain,
% 0.62/0.83      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X7 @ X6)
% 0.62/0.83          | (r2_hidden @ X7 @ X5)
% 0.62/0.83          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.83      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.62/0.83  thf('5', plain,
% 0.62/0.83      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.62/0.83         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.83      inference('simplify', [status(thm)], ['4'])).
% 0.62/0.83  thf('6', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X0 @ sk_C)
% 0.62/0.83          | (r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['3', '5'])).
% 0.62/0.83  thf('7', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '6'])).
% 0.62/0.83  thf(d2_zfmisc_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.62/0.83       ( ![D:$i]:
% 0.62/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.83           ( ?[E:$i,F:$i]:
% 0.62/0.83             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.62/0.83               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.62/0.83  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.62/0.83  thf(zf_stmt_2, axiom,
% 0.62/0.83    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.62/0.83     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.62/0.83       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.62/0.83         ( r2_hidden @ E @ A ) ) ))).
% 0.62/0.83  thf(zf_stmt_3, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.62/0.83       ( ![D:$i]:
% 0.62/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.83           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.62/0.83  thf('8', plain,
% 0.62/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X23 @ X22)
% 0.62/0.83          | (zip_tseitin_0 @ (sk_F_1 @ X23 @ X20 @ X21) @ 
% 0.62/0.83             (sk_E_1 @ X23 @ X20 @ X21) @ X23 @ X20 @ X21)
% 0.62/0.83          | ((X22) != (k2_zfmisc_1 @ X21 @ X20)))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.62/0.83  thf('9', plain,
% 0.62/0.83      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.62/0.83         ((zip_tseitin_0 @ (sk_F_1 @ X23 @ X20 @ X21) @ 
% 0.62/0.83           (sk_E_1 @ X23 @ X20 @ X21) @ X23 @ X20 @ X21)
% 0.62/0.83          | ~ (r2_hidden @ X23 @ (k2_zfmisc_1 @ X21 @ X20)))),
% 0.62/0.83      inference('simplify', [status(thm)], ['8'])).
% 0.62/0.83  thf('10', plain,
% 0.62/0.83      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.62/0.83        (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2 @ sk_B_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '9'])).
% 0.62/0.83  thf('11', plain,
% 0.62/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.62/0.83         (((X13) = (k4_tarski @ X11 @ X12))
% 0.62/0.83          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.83  thf('12', plain,
% 0.62/0.83      (((sk_D_2)
% 0.62/0.83         = (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.62/0.83            (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.62/0.83  thf('13', plain,
% 0.62/0.83      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.62/0.83        (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2 @ sk_B_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '9'])).
% 0.62/0.83  thf('14', plain,
% 0.62/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.62/0.83         ((r2_hidden @ X12 @ X14)
% 0.62/0.83          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.83  thf('15', plain, ((r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.62/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.62/0.83  thf(d2_subset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ( v1_xboole_0 @ A ) =>
% 0.62/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.62/0.83       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.83         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.83  thf('16', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         (~ (r2_hidden @ X27 @ X28)
% 0.62/0.83          | (m1_subset_1 @ X27 @ X28)
% 0.62/0.83          | (v1_xboole_0 @ X28))),
% 0.62/0.83      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.62/0.83  thf(d1_xboole_0, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.83  thf('17', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.83  thf('18', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.62/0.83      inference('clc', [status(thm)], ['16', '17'])).
% 0.62/0.83  thf('19', plain,
% 0.62/0.83      ((m1_subset_1 @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.62/0.83      inference('sup-', [status(thm)], ['15', '18'])).
% 0.62/0.83  thf('20', plain,
% 0.62/0.83      (![X30 : $i, X31 : $i]:
% 0.62/0.83         (~ (m1_subset_1 @ X30 @ sk_B_1)
% 0.62/0.83          | ((sk_D_2) != (k4_tarski @ X31 @ X30))
% 0.62/0.83          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('21', plain,
% 0.62/0.83      (![X0 : $i]:
% 0.62/0.83         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.62/0.83          | ((sk_D_2) != (k4_tarski @ X0 @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.62/0.83  thf('22', plain,
% 0.62/0.83      ((((sk_D_2) != (sk_D_2))
% 0.62/0.83        | ~ (m1_subset_1 @ (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['12', '21'])).
% 0.62/0.83  thf('23', plain,
% 0.62/0.83      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.62/0.83        (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_D_2 @ sk_B_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '9'])).
% 0.62/0.83  thf('24', plain,
% 0.62/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.62/0.83         ((r2_hidden @ X11 @ X15)
% 0.62/0.83          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.62/0.83  thf('25', plain, ((r2_hidden @ (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.62/0.83  thf('26', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i]:
% 0.62/0.83         ((m1_subset_1 @ X27 @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.62/0.83      inference('clc', [status(thm)], ['16', '17'])).
% 0.62/0.83  thf('27', plain, ((m1_subset_1 @ (sk_E_1 @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.62/0.83  thf('28', plain, (((sk_D_2) != (sk_D_2))),
% 0.62/0.83      inference('demod', [status(thm)], ['22', '27'])).
% 0.62/0.83  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.62/0.83  
% 0.62/0.83  % SZS output end Refutation
% 0.62/0.83  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
