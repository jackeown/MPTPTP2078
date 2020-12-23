%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pzd0bHqZ2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:58 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 112 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  361 (1098 expanded)
%              Number of equality atoms :   16 (  46 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('2',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_D_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_D_1 @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k2_tarski @ X23 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ( X16
       != ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X14 @ X15 ) @ ( sk_E_1 @ X17 @ X14 @ X15 ) @ X17 @ X14 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7
        = ( k4_tarski @ X5 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( sk_D_1
    = ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X5 @ X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_B )
      | ( sk_D_1
       != ( k4_tarski @ X27 @ X28 ) )
      | ~ ( r2_hidden @ X28 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C )
      | ( sk_D_1
       != ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_D_1 != sk_D_1 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('26',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_D_1 != sk_D_1 ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9pzd0bHqZ2
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 69 iterations in 0.081s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.36/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.36/0.53  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.36/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(t103_zfmisc_1, conjecture,
% 0.36/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.53     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.36/0.53          ( r2_hidden @ D @ A ) & 
% 0.36/0.53          ( ![E:$i,F:$i]:
% 0.36/0.53            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.36/0.53                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.53        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.36/0.53             ( r2_hidden @ D @ A ) & 
% 0.36/0.53             ( ![E:$i,F:$i]:
% 0.36/0.53               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.36/0.53                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 0.36/0.53  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('2', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t38_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.36/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.36/0.53         ((r1_tarski @ (k2_tarski @ X23 @ X25) @ X26)
% 0.36/0.53          | ~ (r2_hidden @ X25 @ X26)
% 0.36/0.53          | ~ (r2_hidden @ X23 @ X26))),
% 0.36/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X0 @ sk_A)
% 0.36/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_D_1) @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.53  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_D_1 @ sk_D_1) @ sk_A)),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.36/0.53  thf(t12_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      (![X3 : $i, X4 : $i]:
% 0.36/0.53         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.36/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (((k2_xboole_0 @ (k2_tarski @ sk_D_1 @ sk_D_1) @ sk_A) = (sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.53  thf(t11_xboole_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.53         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.36/0.53      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (r1_tarski @ sk_A @ X0)
% 0.36/0.53          | (r1_tarski @ (k2_tarski @ sk_D_1 @ sk_D_1) @ X0))),
% 0.36/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      ((r1_tarski @ (k2_tarski @ sk_D_1 @ sk_D_1) @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['0', '9'])).
% 0.36/0.53  thf('11', plain,
% 0.36/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.53         ((r2_hidden @ X23 @ X24)
% 0.36/0.53          | ~ (r1_tarski @ (k2_tarski @ X23 @ X25) @ X24))),
% 0.36/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.53  thf('12', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.53  thf(d2_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.36/0.53       ( ![D:$i]:
% 0.36/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.53           ( ?[E:$i,F:$i]:
% 0.36/0.53             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.36/0.53               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.36/0.53  thf(zf_stmt_2, axiom,
% 0.36/0.53    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.36/0.53     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.36/0.53       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.36/0.53         ( r2_hidden @ E @ A ) ) ))).
% 0.36/0.53  thf(zf_stmt_3, axiom,
% 0.36/0.53    (![A:$i,B:$i,C:$i]:
% 0.36/0.53     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.36/0.53       ( ![D:$i]:
% 0.36/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.53           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X17 @ X16)
% 0.36/0.53          | (zip_tseitin_0 @ (sk_F_1 @ X17 @ X14 @ X15) @ 
% 0.36/0.53             (sk_E_1 @ X17 @ X14 @ X15) @ X17 @ X14 @ X15)
% 0.36/0.53          | ((X16) != (k2_zfmisc_1 @ X15 @ X14)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.36/0.53         ((zip_tseitin_0 @ (sk_F_1 @ X17 @ X14 @ X15) @ 
% 0.36/0.53           (sk_E_1 @ X17 @ X14 @ X15) @ X17 @ X14 @ X15)
% 0.36/0.53          | ~ (r2_hidden @ X17 @ (k2_zfmisc_1 @ X15 @ X14)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.53  thf('15', plain,
% 0.36/0.53      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.36/0.53        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         (((X7) = (k4_tarski @ X5 @ X6))
% 0.36/0.53          | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      (((sk_D_1)
% 0.36/0.53         = (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.36/0.53            (sk_F_1 @ sk_D_1 @ sk_C @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.36/0.53        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         ((r2_hidden @ X5 @ X9) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.53  thf('20', plain, ((r2_hidden @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      (![X27 : $i, X28 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X27 @ sk_B)
% 0.36/0.53          | ((sk_D_1) != (k4_tarski @ X27 @ X28))
% 0.36/0.53          | ~ (r2_hidden @ X28 @ sk_C))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         (~ (r2_hidden @ X0 @ sk_C)
% 0.36/0.53          | ((sk_D_1) != (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      ((((sk_D_1) != (sk_D_1))
% 0.36/0.53        | ~ (r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C))),
% 0.36/0.53      inference('sup-', [status(thm)], ['17', '22'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.36/0.53        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.36/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.53         ((r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X5 @ X7 @ X8 @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.53  thf('26', plain, ((r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C)),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain, (((sk_D_1) != (sk_D_1))),
% 0.36/0.53      inference('demod', [status(thm)], ['23', '26'])).
% 0.36/0.53  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
