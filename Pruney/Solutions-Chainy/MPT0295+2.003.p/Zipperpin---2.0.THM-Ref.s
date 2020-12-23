%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5fnko8H8EH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:57 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 109 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  357 ( 960 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    = ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('4',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X23 ) @ X25 )
      | ~ ( r2_hidden @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_D_1 ) @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ ( k1_tarski @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D_1 @ ( k2_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    r2_hidden @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['2','11'])).

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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X16 @ X17 ) @ ( sk_E_1 @ X19 @ X16 @ X17 ) @ X19 @ X16 @ X17 )
      | ( X18
       != ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X19 @ X16 @ X17 ) @ ( sk_E_1 @ X19 @ X16 @ X17 ) @ X19 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9
        = ( k4_tarski @ X7 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( sk_D_1
    = ( k4_tarski @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_1 @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_D_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['12','14'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X7 @ X11 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_1 @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_B )
      | ( sk_D_1
       != ( k4_tarski @ X26 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_C ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11 ) ) ),
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
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5fnko8H8EH
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.99  % Solved by: fo/fo7.sh
% 0.75/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.99  % done 628 iterations in 0.529s
% 0.75/0.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.99  % SZS output start Refutation
% 0.75/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.99  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.75/0.99  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.99  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.99  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.99  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.75/0.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.75/0.99  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.75/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.99  thf(t103_zfmisc_1, conjecture,
% 0.75/0.99    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.99     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.75/0.99          ( r2_hidden @ D @ A ) & 
% 0.75/0.99          ( ![E:$i,F:$i]:
% 0.75/0.99            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.75/0.99                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.75/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.99        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.75/0.99             ( r2_hidden @ D @ A ) & 
% 0.75/0.99             ( ![E:$i,F:$i]:
% 0.75/0.99               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.75/0.99                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 0.75/0.99    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 0.75/0.99  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf(t12_xboole_1, axiom,
% 0.75/0.99    (![A:$i,B:$i]:
% 0.75/0.99     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.99  thf('1', plain,
% 0.75/0.99      (![X5 : $i, X6 : $i]:
% 0.75/0.99         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.75/0.99      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.99  thf('2', plain,
% 0.75/0.99      (((k2_xboole_0 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.75/0.99         = (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/0.99  thf(commutativity_k2_xboole_0, axiom,
% 0.75/0.99    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.75/0.99  thf('3', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.75/0.99      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.75/0.99  thf('4', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf(l1_zfmisc_1, axiom,
% 0.75/0.99    (![A:$i,B:$i]:
% 0.75/0.99     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.75/0.99  thf('5', plain,
% 0.75/0.99      (![X23 : $i, X25 : $i]:
% 0.75/0.99         ((r1_tarski @ (k1_tarski @ X23) @ X25) | ~ (r2_hidden @ X23 @ X25))),
% 0.75/0.99      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.75/0.99  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.75/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.99  thf(t10_xboole_1, axiom,
% 0.75/0.99    (![A:$i,B:$i,C:$i]:
% 0.75/0.99     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.75/0.99  thf('7', plain,
% 0.75/0.99      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.99         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.75/0.99      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.75/0.99  thf('8', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (r1_tarski @ (k1_tarski @ sk_D_1) @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.99  thf('9', plain,
% 0.75/0.99      (![X23 : $i, X24 : $i]:
% 0.75/0.99         ((r2_hidden @ X23 @ X24) | ~ (r1_tarski @ (k1_tarski @ X23) @ X24))),
% 0.75/0.99      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.75/0.99  thf('10', plain,
% 0.75/0.99      (![X0 : $i]: (r2_hidden @ sk_D_1 @ (k2_xboole_0 @ X0 @ sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.99  thf('11', plain,
% 0.75/0.99      (![X0 : $i]: (r2_hidden @ sk_D_1 @ (k2_xboole_0 @ sk_A @ X0))),
% 0.75/0.99      inference('sup+', [status(thm)], ['3', '10'])).
% 0.75/0.99  thf('12', plain, ((r2_hidden @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.75/0.99      inference('sup+', [status(thm)], ['2', '11'])).
% 0.75/0.99  thf(d2_zfmisc_1, axiom,
% 0.75/0.99    (![A:$i,B:$i,C:$i]:
% 0.75/0.99     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.75/0.99       ( ![D:$i]:
% 0.75/0.99         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.99           ( ?[E:$i,F:$i]:
% 0.75/0.99             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.75/0.99               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.75/0.99  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.75/0.99  thf(zf_stmt_2, axiom,
% 0.75/0.99    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.75/0.99     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.75/0.99       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.75/0.99         ( r2_hidden @ E @ A ) ) ))).
% 0.75/0.99  thf(zf_stmt_3, axiom,
% 0.75/0.99    (![A:$i,B:$i,C:$i]:
% 0.75/0.99     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.75/0.99       ( ![D:$i]:
% 0.75/0.99         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.99           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.75/0.99  thf('13', plain,
% 0.75/0.99      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.99         (~ (r2_hidden @ X19 @ X18)
% 0.75/0.99          | (zip_tseitin_0 @ (sk_F_1 @ X19 @ X16 @ X17) @ 
% 0.75/0.99             (sk_E_1 @ X19 @ X16 @ X17) @ X19 @ X16 @ X17)
% 0.75/0.99          | ((X18) != (k2_zfmisc_1 @ X17 @ X16)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.99  thf('14', plain,
% 0.75/0.99      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.75/0.99         ((zip_tseitin_0 @ (sk_F_1 @ X19 @ X16 @ X17) @ 
% 0.75/0.99           (sk_E_1 @ X19 @ X16 @ X17) @ X19 @ X16 @ X17)
% 0.75/0.99          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.75/0.99      inference('simplify', [status(thm)], ['13'])).
% 0.75/0.99  thf('15', plain,
% 0.75/0.99      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.75/0.99        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.75/0.99      inference('sup-', [status(thm)], ['12', '14'])).
% 0.75/0.99  thf('16', plain,
% 0.75/0.99      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.99         (((X9) = (k4_tarski @ X7 @ X8))
% 0.75/0.99          | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.99  thf('17', plain,
% 0.75/0.99      (((sk_D_1)
% 0.75/0.99         = (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.75/0.99            (sk_F_1 @ sk_D_1 @ sk_C @ sk_B)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.99  thf('18', plain,
% 0.75/0.99      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.75/0.99        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.75/0.99      inference('sup-', [status(thm)], ['12', '14'])).
% 0.75/0.99  thf('19', plain,
% 0.75/0.99      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.99         ((r2_hidden @ X7 @ X11) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.99  thf('20', plain, ((r2_hidden @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_B)),
% 0.75/0.99      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.99  thf('21', plain,
% 0.75/0.99      (![X26 : $i, X27 : $i]:
% 0.75/0.99         (~ (r2_hidden @ X26 @ sk_B)
% 0.75/0.99          | ((sk_D_1) != (k4_tarski @ X26 @ X27))
% 0.75/0.99          | ~ (r2_hidden @ X27 @ sk_C))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('22', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (r2_hidden @ X0 @ sk_C)
% 0.75/0.99          | ((sk_D_1) != (k4_tarski @ (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ X0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['20', '21'])).
% 0.75/0.99  thf('23', plain,
% 0.75/0.99      ((((sk_D_1) != (sk_D_1))
% 0.75/0.99        | ~ (r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C))),
% 0.75/0.99      inference('sup-', [status(thm)], ['17', '22'])).
% 0.75/0.99  thf('24', plain,
% 0.75/0.99      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ 
% 0.75/0.99        (sk_E_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_D_1 @ sk_C @ sk_B)),
% 0.75/0.99      inference('sup-', [status(thm)], ['12', '14'])).
% 0.75/0.99  thf('25', plain,
% 0.75/0.99      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.99         ((r2_hidden @ X8 @ X10) | ~ (zip_tseitin_0 @ X8 @ X7 @ X9 @ X10 @ X11))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.99  thf('26', plain, ((r2_hidden @ (sk_F_1 @ sk_D_1 @ sk_C @ sk_B) @ sk_C)),
% 0.75/0.99      inference('sup-', [status(thm)], ['24', '25'])).
% 0.75/0.99  thf('27', plain, (((sk_D_1) != (sk_D_1))),
% 0.75/0.99      inference('demod', [status(thm)], ['23', '26'])).
% 0.75/0.99  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.75/0.99  
% 0.75/0.99  % SZS output end Refutation
% 0.75/0.99  
% 0.75/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
