%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BuiVA0W6pH

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 121 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  429 ( 930 expanded)
%              Number of equality atoms :   87 ( 180 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) )
      = X25 ) ),
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

thf('10',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X25: $i,X27: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X25 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('15',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 != X20 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_tarski @ X20 ) )
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X20 ) )
     != ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X20 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['24','30'])).

thf('32',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','31'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X20: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X20 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('38',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['9','38'])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_A )
      | ~ ( r2_hidden @ sk_A @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['24','30'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X20: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X20 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('47',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BuiVA0W6pH
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:00:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 98 iterations in 0.033s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(d1_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('1', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.48  thf(t20_mcart_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.48       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.48          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.48  thf('2', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t7_mcart_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X25 : $i, X26 : $i]: ((k1_mcart_1 @ (k4_tarski @ X25 @ X26)) = (X25))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('4', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.48  thf('8', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.20/0.48         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.20/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.20/0.48  thf('11', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X25 : $i, X27 : $i]: ((k2_mcart_1 @ (k4_tarski @ X25 @ X27)) = (X27))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.48  thf('13', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.20/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf(t9_mcart_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.48                 ( ![C:$i,D:$i]:
% 0.20/0.48                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.48                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         (((X28) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X29 @ X28)
% 0.20/0.48          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (((sk_B @ X0) != (sk_A))
% 0.20/0.48           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.48           | ((X0) = (k1_xboole_0))))
% 0.20/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X28 : $i]:
% 0.20/0.48         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.20/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.48          | ((X10) = (X7))
% 0.20/0.48          | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X7 : $i, X10 : $i]:
% 0.20/0.48         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.48          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.48  thf(t20_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48         ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ( A ) != ( B ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X20 : $i, X21 : $i]:
% 0.20/0.48         (((X21) != (X20))
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X21) @ (k1_tarski @ X20))
% 0.20/0.48              != (k1_tarski @ X21)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X20 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X20))
% 0.20/0.48           != (k1_tarski @ X20))),
% 0.20/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.48  thf(t22_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.20/0.48  thf(t46_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.48  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, (![X20 : $i]: ((k1_xboole_0) != (k1_tarski @ X20))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf('31', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['24', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.20/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain, (![X20 : $i]: ((k1_xboole_0) != (k1_tarski @ X20))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['5'])).
% 0.20/0.48  thf('38', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain, (((sk_A) = (k4_tarski @ sk_A @ sk_C_1))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['9', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         (((X28) = (k1_xboole_0))
% 0.20/0.48          | ~ (r2_hidden @ X30 @ X28)
% 0.20/0.48          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B @ X0) != (sk_A))
% 0.20/0.48          | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.48        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '41'])).
% 0.20/0.48  thf('43', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.48      inference('clc', [status(thm)], ['24', '30'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.48  thf('46', plain, (![X20 : $i]: ((k1_xboole_0) != (k1_tarski @ X20))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf('47', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
