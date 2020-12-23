%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guf2AZ4cnQ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:57 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 106 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  460 (1088 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) )
      | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

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

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X27 @ X24 @ X25 ) @ ( sk_E_1 @ X27 @ X24 @ X25 ) @ X27 @ X24 @ X25 )
      | ( X26
       != ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X27 @ X24 @ X25 ) @ ( sk_E_1 @ X27 @ X24 @ X25 ) @ X27 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ X0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17
        = ( k4_tarski @ X15 @ X16 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k4_tarski @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ X0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X15 @ X19 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ sk_B_1 )
      | ( sk_D_1
       != ( k4_tarski @ X31 @ X32 ) )
      | ~ ( r2_hidden @ X32 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ sk_C_2 )
      | ( sk_D_1
       != ( k4_tarski @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_D_1 != X0 )
      | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
      | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ ( sk_E_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ X0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ X18 )
      | ~ ( zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_F_1 @ X0 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ),
    inference(clc,[status(thm)],['22','25'])).

thf('27',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('32',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['30','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.guf2AZ4cnQ
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 829 iterations in 0.692s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.00/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.20  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.00/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.20  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 1.00/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.20  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.00/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.20  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.00/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.20  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.00/1.20  thf(t3_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.00/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf(d1_tarski, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.00/1.20       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X13 @ X12)
% 1.00/1.20          | ((X13) = (X10))
% 1.00/1.20          | ((X12) != (k1_tarski @ X10)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X10 : $i, X13 : $i]:
% 1.00/1.20         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['1'])).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.00/1.20          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['0', '2'])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ X1)
% 1.00/1.20          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 1.00/1.20          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['3', '4'])).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 1.00/1.20      inference('simplify', [status(thm)], ['5'])).
% 1.00/1.20  thf(t103_zfmisc_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.00/1.20          ( r2_hidden @ D @ A ) & 
% 1.00/1.20          ( ![E:$i,F:$i]:
% 1.00/1.20            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 1.00/1.20                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.20        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 1.00/1.20             ( r2_hidden @ D @ A ) & 
% 1.00/1.20             ( ![E:$i,F:$i]:
% 1.00/1.20               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 1.00/1.20                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 1.00/1.20  thf('7', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(t63_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.00/1.20       ( r1_xboole_0 @ A @ C ) ))).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.00/1.20         (~ (r1_tarski @ X7 @ X8)
% 1.00/1.20          | ~ (r1_xboole_0 @ X8 @ X9)
% 1.00/1.20          | (r1_xboole_0 @ X7 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.00/1.20  thf('9', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ X0)
% 1.00/1.20          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2) @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2))
% 1.00/1.20          | (r1_xboole_0 @ sk_A @ (k1_tarski @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['6', '9'])).
% 1.00/1.20  thf(d2_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20           ( ?[E:$i,F:$i]:
% 1.00/1.20             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 1.00/1.20               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.00/1.20  thf(zf_stmt_2, axiom,
% 1.00/1.20    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 1.00/1.20     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 1.00/1.20       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 1.00/1.20         ( r2_hidden @ E @ A ) ) ))).
% 1.00/1.20  thf(zf_stmt_3, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X27 @ X26)
% 1.00/1.20          | (zip_tseitin_0 @ (sk_F_1 @ X27 @ X24 @ X25) @ 
% 1.00/1.20             (sk_E_1 @ X27 @ X24 @ X25) @ X27 @ X24 @ X25)
% 1.00/1.20          | ((X26) != (k2_zfmisc_1 @ X25 @ X24)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (![X24 : $i, X25 : $i, X27 : $i]:
% 1.00/1.20         ((zip_tseitin_0 @ (sk_F_1 @ X27 @ X24 @ X25) @ 
% 1.00/1.20           (sk_E_1 @ X27 @ X24 @ X25) @ X27 @ X24 @ X25)
% 1.00/1.20          | ~ (r2_hidden @ X27 @ (k2_zfmisc_1 @ X25 @ X24)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['11'])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | (zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1) @ 
% 1.00/1.20             (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ X0 @ sk_C_2 @ sk_B_1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '12'])).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.00/1.20         (((X17) = (k4_tarski @ X15 @ X16))
% 1.00/1.20          | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | ((X0)
% 1.00/1.20              = (k4_tarski @ (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ 
% 1.00/1.20                 (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | (zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1) @ 
% 1.00/1.20             (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ X0 @ sk_C_2 @ sk_B_1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '12'])).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.00/1.20         ((r2_hidden @ X15 @ X19)
% 1.00/1.20          | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['16', '17'])).
% 1.00/1.20  thf('19', plain,
% 1.00/1.20      (![X31 : $i, X32 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X31 @ sk_B_1)
% 1.00/1.20          | ((sk_D_1) != (k4_tarski @ X31 @ X32))
% 1.00/1.20          | ~ (r2_hidden @ X32 @ sk_C_2))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('20', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | ~ (r2_hidden @ X1 @ sk_C_2)
% 1.00/1.20          | ((sk_D_1) != (k4_tarski @ (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ X1)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (((sk_D_1) != (X0))
% 1.00/1.20          | (r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | ~ (r2_hidden @ (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1) @ sk_C_2)
% 1.00/1.20          | (r1_xboole_0 @ sk_A @ (k1_tarski @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '20'])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      ((~ (r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C_2 @ sk_B_1) @ sk_C_2)
% 1.00/1.20        | (r1_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | (zip_tseitin_0 @ (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1) @ 
% 1.00/1.20             (sk_E_1 @ X0 @ sk_C_2 @ sk_B_1) @ X0 @ sk_C_2 @ sk_B_1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '12'])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.00/1.20         ((r2_hidden @ X16 @ X18)
% 1.00/1.20          | ~ (zip_tseitin_0 @ X16 @ X15 @ X17 @ X18 @ X19))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ sk_A @ (k1_tarski @ X0))
% 1.00/1.20          | (r2_hidden @ (sk_F_1 @ X0 @ sk_C_2 @ sk_B_1) @ sk_C_2))),
% 1.00/1.20      inference('sup-', [status(thm)], ['23', '24'])).
% 1.00/1.20  thf('26', plain, ((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))),
% 1.00/1.20      inference('clc', [status(thm)], ['22', '25'])).
% 1.00/1.20  thf('27', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('28', plain,
% 1.00/1.20      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X5 @ X3)
% 1.00/1.20          | ~ (r2_hidden @ X5 @ X6)
% 1.00/1.20          | ~ (r1_xboole_0 @ X3 @ X6))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (![X0 : $i]: (~ (r1_xboole_0 @ sk_A @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['27', '28'])).
% 1.00/1.20  thf('30', plain, (~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['26', '29'])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.20         (((X11) != (X10))
% 1.00/1.20          | (r2_hidden @ X11 @ X12)
% 1.00/1.20          | ((X12) != (k1_tarski @ X10)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d1_tarski])).
% 1.00/1.20  thf('32', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 1.00/1.20      inference('simplify', [status(thm)], ['31'])).
% 1.00/1.20  thf('33', plain, ($false), inference('demod', [status(thm)], ['30', '32'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
