%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JVP1EJkMwQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   54 (  73 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  339 ( 533 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ( X18
        = ( k2_zfmisc_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X18 @ X14 @ X15 ) @ ( sk_E @ X18 @ X14 @ X15 ) @ ( sk_D @ X18 @ X14 @ X15 ) @ X14 @ X15 )
      | ( r2_hidden @ ( sk_D @ X18 @ X14 @ X15 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('3',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r1_xboole_0 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

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

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( r2_hidden @ ( sk_C_1 @ X25 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r1_xboole_0 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( sk_C_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X27: $i] :
      ~ ( r2_hidden @ X27 @ sk_A ) ),
    inference(demod,[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ sk_A @ X1 @ X0 ) @ X1 )
      | ( sk_A
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X21 @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('24',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JVP1EJkMwQ
% 0.16/0.37  % Computer   : n013.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 18:01:55 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.54  % Solved by: fo/fo7.sh
% 0.23/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.54  % done 104 iterations in 0.060s
% 0.23/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.54  % SZS output start Refutation
% 0.23/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.23/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.23/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.23/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.54  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.23/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.54  thf(d2_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.23/0.54       ( ![D:$i]:
% 0.23/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.54           ( ?[E:$i,F:$i]:
% 0.23/0.54             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.23/0.54               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.23/0.54  thf(zf_stmt_1, axiom,
% 0.23/0.54    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.23/0.54     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.23/0.54       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.23/0.54         ( r2_hidden @ E @ A ) ) ))).
% 0.23/0.54  thf(zf_stmt_2, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.23/0.54       ( ![D:$i]:
% 0.23/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.54           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.23/0.54  thf('0', plain,
% 0.23/0.54      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.23/0.54         (((X18) = (k2_zfmisc_1 @ X15 @ X14))
% 0.23/0.54          | (zip_tseitin_0 @ (sk_F @ X18 @ X14 @ X15) @ 
% 0.23/0.54             (sk_E @ X18 @ X14 @ X15) @ (sk_D @ X18 @ X14 @ X15) @ X14 @ X15)
% 0.23/0.54          | (r2_hidden @ (sk_D @ X18 @ X14 @ X15) @ X18))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.54  thf('1', plain,
% 0.23/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.54         ((r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.54  thf('2', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.23/0.54          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.23/0.54          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf(t1_mcart_1, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.54          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_3, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.54             ( ![B:$i]:
% 0.23/0.54               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.23/0.54  thf('3', plain,
% 0.23/0.54      (![X27 : $i]: (~ (r2_hidden @ X27 @ sk_A) | ~ (r1_xboole_0 @ X27 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.54  thf(t3_xboole_0, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.54  thf('4', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.54  thf(t7_tarski, axiom,
% 0.23/0.54    (![A:$i,B:$i]:
% 0.23/0.54     ( ~( ( r2_hidden @ A @ B ) & 
% 0.23/0.54          ( ![C:$i]:
% 0.23/0.54            ( ~( ( r2_hidden @ C @ B ) & 
% 0.23/0.54                 ( ![D:$i]:
% 0.23/0.54                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.23/0.54  thf('5', plain,
% 0.23/0.54      (![X24 : $i, X25 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X24 @ X25) | (r2_hidden @ (sk_C_1 @ X25) @ X25))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.23/0.54  thf('6', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.54  thf('7', plain,
% 0.23/0.54      (![X27 : $i]: (~ (r2_hidden @ X27 @ sk_A) | ~ (r1_xboole_0 @ X27 @ sk_A))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.54  thf('8', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X0 @ sk_A) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.23/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X24 @ X25)
% 0.23/0.54          | ~ (r2_hidden @ X26 @ X25)
% 0.23/0.54          | ~ (r2_hidden @ X26 @ (sk_C_1 @ X25)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t7_tarski])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.23/0.54      inference('condensation', [status(thm)], ['11'])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.23/0.54          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['10', '12'])).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X0 : $i]:
% 0.23/0.54         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.23/0.54          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '13'])).
% 0.23/0.54  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.23/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.23/0.54  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['8', '15'])).
% 0.23/0.54  thf('17', plain, (![X27 : $i]: ~ (r2_hidden @ X27 @ sk_A)),
% 0.23/0.54      inference('demod', [status(thm)], ['3', '16'])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_F @ sk_A @ X1 @ X0) @ X1)
% 0.23/0.54          | ((sk_A) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['2', '17'])).
% 0.23/0.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.54  thf('19', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.23/0.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.54  thf(t55_zfmisc_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.23/0.54  thf('20', plain,
% 0.23/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.54         (~ (r1_xboole_0 @ (k2_tarski @ X21 @ X22) @ X23)
% 0.23/0.54          | ~ (r2_hidden @ X21 @ X23))),
% 0.23/0.54      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.23/0.54  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('22', plain, (![X0 : $i]: ((sk_A) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.23/0.54  thf('23', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.23/0.54          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.23/0.54          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.54  thf('24', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('25', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r2_hidden @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.23/0.54          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.23/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.23/0.54  thf('26', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.54  thf('27', plain,
% 0.23/0.54      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.54  thf('28', plain, (((k1_xboole_0) = (sk_A))),
% 0.23/0.54      inference('sup+', [status(thm)], ['22', '27'])).
% 0.23/0.54  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.54  thf('30', plain, ($false),
% 0.23/0.54      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
