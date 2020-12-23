%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QrMWUXCx48

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:00 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 192 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  482 (1531 expanded)
%              Number of equality atoms :   93 ( 258 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) )
        = ( k1_tarski @ X16 ) )
      | ( X16 = X17 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ~ ( r2_hidden @ X18 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X19 @ ( k1_tarski @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 != X15 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X15 ) )
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X15 ) @ ( k1_tarski @ X15 ) )
     != ( k1_tarski @ X15 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X27: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

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

thf('18',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k4_tarski @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','12'])).

thf('30',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('37',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ( ( sk_B @ X27 )
       != ( k4_tarski @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['5','12'])).

thf('44',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('50',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','50'])).

thf('52',plain,(
    ! [X15: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X15 ) ) ),
    inference(demod,[status(thm)],['7','11'])).

thf('53',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QrMWUXCx48
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.53  % Solved by: fo/fo7.sh
% 0.37/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.53  % done 235 iterations in 0.078s
% 0.37/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.53  % SZS output start Refutation
% 0.37/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.53  thf(t9_mcart_1, axiom,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.37/0.53          ( ![B:$i]:
% 0.37/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.37/0.53                 ( ![C:$i,D:$i]:
% 0.37/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.37/0.53                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.53  thf('0', plain,
% 0.37/0.53      (![X27 : $i]:
% 0.37/0.53         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.37/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.53  thf(t20_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.37/0.53         ( k1_tarski @ A ) ) <=>
% 0.37/0.53       ( ( A ) != ( B ) ) ))).
% 0.37/0.53  thf('1', plain,
% 0.37/0.53      (![X16 : $i, X17 : $i]:
% 0.37/0.53         (((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17))
% 0.37/0.53            = (k1_tarski @ X16))
% 0.37/0.53          | ((X16) = (X17)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.53  thf(t64_zfmisc_1, axiom,
% 0.37/0.53    (![A:$i,B:$i,C:$i]:
% 0.37/0.53     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.37/0.53       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.37/0.53  thf('2', plain,
% 0.37/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.37/0.53         (((X18) != (X20))
% 0.37/0.53          | ~ (r2_hidden @ X18 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20))))),
% 0.37/0.53      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.37/0.53  thf('3', plain,
% 0.37/0.53      (![X19 : $i, X20 : $i]:
% 0.37/0.53         ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X19 @ (k1_tarski @ X20)))),
% 0.37/0.53      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.53  thf('4', plain,
% 0.37/0.53      (![X0 : $i, X1 : $i]:
% 0.37/0.53         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.37/0.53      inference('sup-', [status(thm)], ['1', '3'])).
% 0.37/0.53  thf('5', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.37/0.53          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.37/0.53  thf('6', plain,
% 0.37/0.53      (![X15 : $i, X16 : $i]:
% 0.37/0.53         (((X16) != (X15))
% 0.37/0.53          | ((k4_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X15))
% 0.37/0.53              != (k1_tarski @ X16)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.37/0.53  thf('7', plain,
% 0.37/0.53      (![X15 : $i]:
% 0.37/0.53         ((k4_xboole_0 @ (k1_tarski @ X15) @ (k1_tarski @ X15))
% 0.37/0.53           != (k1_tarski @ X15))),
% 0.37/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.37/0.53  thf(d10_xboole_0, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.53  thf('8', plain,
% 0.37/0.53      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.37/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.53  thf('9', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.37/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.53  thf(l32_xboole_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.53  thf('10', plain,
% 0.37/0.53      (![X4 : $i, X6 : $i]:
% 0.37/0.53         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.37/0.53  thf('11', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.53  thf('12', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.53      inference('demod', [status(thm)], ['7', '11'])).
% 0.37/0.53  thf('13', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.37/0.53      inference('clc', [status(thm)], ['5', '12'])).
% 0.37/0.53  thf('14', plain,
% 0.37/0.53      (![X27 : $i]:
% 0.37/0.53         (((X27) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X27) @ X27))),
% 0.37/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.53  thf('15', plain,
% 0.37/0.53      (![X0 : $i]:
% 0.37/0.53         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.37/0.53          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.37/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.53  thf('16', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.53      inference('demod', [status(thm)], ['7', '11'])).
% 0.37/0.53  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.53  thf(t20_mcart_1, conjecture,
% 0.37/0.53    (![A:$i]:
% 0.37/0.53     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.53       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.37/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.53    (~( ![A:$i]:
% 0.37/0.53        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.37/0.53          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.37/0.53    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.37/0.53  thf('18', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf(t7_mcart_1, axiom,
% 0.37/0.53    (![A:$i,B:$i]:
% 0.37/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.37/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.37/0.53  thf('19', plain,
% 0.37/0.53      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.53  thf('20', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.37/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.37/0.53  thf('21', plain,
% 0.37/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('22', plain,
% 0.37/0.53      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('split', [status(esa)], ['21'])).
% 0.37/0.53  thf('23', plain,
% 0.37/0.53      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['20', '22'])).
% 0.37/0.53  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('25', plain,
% 0.37/0.53      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.37/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.53  thf('26', plain,
% 0.37/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.53         (((X27) = (k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ X29 @ X27)
% 0.37/0.53          | ((sk_B @ X27) != (k4_tarski @ X29 @ X28)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.53  thf('27', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          (((sk_B @ X0) != (sk_A))
% 0.37/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.37/0.53           | ((X0) = (k1_xboole_0))))
% 0.37/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.53  thf('28', plain,
% 0.37/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.37/0.53         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.37/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['17', '27'])).
% 0.37/0.53  thf('29', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.37/0.53      inference('clc', [status(thm)], ['5', '12'])).
% 0.37/0.53  thf('30', plain,
% 0.37/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.37/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.37/0.53  thf('31', plain,
% 0.37/0.53      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.53         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.53  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.37/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.37/0.53  thf('33', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('34', plain,
% 0.37/0.53      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.37/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.37/0.53  thf('35', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.37/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.53  thf('36', plain,
% 0.37/0.53      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('split', [status(esa)], ['21'])).
% 0.37/0.53  thf('37', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.53  thf('38', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.37/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.53  thf('39', plain,
% 0.37/0.53      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.37/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup+', [status(thm)], ['37', '38'])).
% 0.37/0.53  thf('40', plain,
% 0.37/0.53      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.53         (((X27) = (k1_xboole_0))
% 0.37/0.53          | ~ (r2_hidden @ X28 @ X27)
% 0.37/0.53          | ((sk_B @ X27) != (k4_tarski @ X29 @ X28)))),
% 0.37/0.53      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.37/0.53  thf('41', plain,
% 0.37/0.53      ((![X0 : $i]:
% 0.37/0.53          (((sk_B @ X0) != (sk_A))
% 0.37/0.53           | ~ (r2_hidden @ sk_A @ X0)
% 0.37/0.53           | ((X0) = (k1_xboole_0))))
% 0.37/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.53  thf('42', plain,
% 0.37/0.53      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.37/0.53         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.37/0.53         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.53      inference('sup-', [status(thm)], ['32', '41'])).
% 0.37/0.53  thf('43', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.37/0.53      inference('clc', [status(thm)], ['5', '12'])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.37/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.37/0.54         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.54  thf('46', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.54      inference('demod', [status(thm)], ['7', '11'])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.54  thf('48', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['47'])).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.37/0.54      inference('split', [status(esa)], ['21'])).
% 0.37/0.54  thf('50', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['48', '49'])).
% 0.37/0.54  thf('51', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['31', '50'])).
% 0.37/0.54  thf('52', plain, (![X15 : $i]: ((k1_xboole_0) != (k1_tarski @ X15))),
% 0.37/0.54      inference('demod', [status(thm)], ['7', '11'])).
% 0.37/0.54  thf('53', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.54  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
