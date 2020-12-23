%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qEsbYroRsu

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 101 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  371 ( 749 expanded)
%              Number of equality atoms :   71 ( 146 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('2',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('4',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('18',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('19',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ( ( sk_B @ X11 )
       != ( k4_tarski @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('32',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('34',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['9','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( ( sk_B @ X11 )
       != ( k4_tarski @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['20','23'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qEsbYroRsu
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 59 iterations in 0.012s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(d1_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('1', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf(t20_mcart_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.50  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.50  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('12', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf(t9_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.50                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X11 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X1 : $i, X4 : $i]:
% 0.20/0.50         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.50  thf(idempotence_k2_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.50  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.20/0.50  thf(t49_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.50  thf('23', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X12 @ X11)
% 0.20/0.50          | ((sk_B @ X11) != (k4_tarski @ X13 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((X0) != (k4_tarski @ X2 @ X1))
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         (((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i]:
% 0.20/0.50         ~ (r2_hidden @ X1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '29'])).
% 0.20/0.50  thf('31', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.20/0.50      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.50  thf('32', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['5'])).
% 0.20/0.50  thf('34', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['9', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X13 @ X11)
% 0.20/0.50          | ((sk_B @ X11) != (k4_tarski @ X13 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_B @ X0) != (sk_A))
% 0.20/0.50          | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50          | ((X0) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '37'])).
% 0.20/0.50  thf('39', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.20/0.50  thf('42', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('43', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
