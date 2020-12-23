%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D3cdfQcKub

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:30 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   49 (  85 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  344 ( 819 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X16 @ X17 ) @ ( sk_E_1 @ X19 @ X16 @ X17 ) @ X19 @ X16 @ X17 )
      | ( X18
       != ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X16 @ X17 ) @ ( sk_E_1 @ X19 @ X16 @ X17 ) @ X19 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_D_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9
        = ( k4_tarski @ X7 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,
    ( sk_D_1
    = ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_D_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( m1_subset_1 @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B_1 )
      | ( sk_D_1
       != ( k4_tarski @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( sk_D_1
       != ( k4_tarski @ X0 @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ~ ( m1_subset_1 @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_D_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X7 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('24',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_D_1 != sk_D_1 ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.D3cdfQcKub
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 179 iterations in 0.230s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.45/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.65  thf(t65_subset_1, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ~( ( r2_hidden @ D @ C ) & 
% 0.45/0.65          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.45/0.65          ( ![E:$i]:
% 0.45/0.65            ( ( m1_subset_1 @ E @ A ) =>
% 0.45/0.65              ( ![F:$i]:
% 0.45/0.65                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65        ( ~( ( r2_hidden @ D @ C ) & 
% 0.45/0.65             ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.45/0.65             ( ![E:$i]:
% 0.45/0.65               ( ( m1_subset_1 @ E @ A ) =>
% 0.45/0.65                 ( ![F:$i]:
% 0.45/0.65                   ( ( m1_subset_1 @ F @ B ) =>
% 0.45/0.65                     ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t65_subset_1])).
% 0.45/0.65  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(d3_tarski, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X3 @ X4)
% 0.45/0.65          | (r2_hidden @ X3 @ X5)
% 0.45/0.65          | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.45/0.65          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.65  thf('4', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.65  thf(d2_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ?[E:$i,F:$i]:
% 0.45/0.65             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.65               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_2, axiom,
% 0.45/0.65    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.45/0.65       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.45/0.65         ( r2_hidden @ E @ A ) ) ))).
% 0.45/0.65  thf(zf_stmt_3, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X19 @ X18)
% 0.45/0.65          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X16 @ X17) @ 
% 0.45/0.65             (sk_E_1 @ X19 @ X16 @ X17) @ X19 @ X16 @ X17)
% 0.45/0.65          | ((X18) != (k2_zfmisc_1 @ X17 @ X16)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ (sk_F_1 @ X19 @ X16 @ X17) @ 
% 0.45/0.65           (sk_E_1 @ X19 @ X16 @ X17) @ X19 @ X16 @ X17)
% 0.45/0.65          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.65        (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_D_1 @ sk_B_1 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         (((X9) = (k4_tarski @ X7 @ X8))
% 0.45/0.65          | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (((sk_D_1)
% 0.45/0.65         = (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.65            (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.65        (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_D_1 @ sk_B_1 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         ((r2_hidden @ X8 @ X10) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('12', plain, ((r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(d2_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.65       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.65         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X23 @ X24)
% 0.45/0.65          | (m1_subset_1 @ X23 @ X24)
% 0.45/0.65          | (v1_xboole_0 @ X24))),
% 0.45/0.65      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.65  thf(d1_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.45/0.65      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      ((m1_subset_1 @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X26 : $i, X27 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X26 @ sk_B_1)
% 0.45/0.65          | ((sk_D_1) != (k4_tarski @ X27 @ X26))
% 0.45/0.65          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.45/0.65          | ((sk_D_1) != (k4_tarski @ X0 @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((((sk_D_1) != (sk_D_1))
% 0.45/0.65        | ~ (m1_subset_1 @ (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['9', '18'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ 
% 0.45/0.65        (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_D_1 @ sk_B_1 @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.65         ((r2_hidden @ X7 @ X11) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('22', plain, ((r2_hidden @ (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X23 @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.45/0.65      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf('24', plain, ((m1_subset_1 @ (sk_E_1 @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 0.45/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.65  thf('25', plain, (((sk_D_1) != (sk_D_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['19', '24'])).
% 0.45/0.65  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
