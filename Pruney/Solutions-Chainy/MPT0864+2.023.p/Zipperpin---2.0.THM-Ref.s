%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buKjQXbK85

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 125 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  388 ( 995 expanded)
%              Number of equality atoms :   71 ( 193 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
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
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('10',plain,(
    ! [X29: $i,X31: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X29 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('15',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('17',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ( ( sk_B @ X32 )
       != ( k4_tarski @ X34 @ X33 ) ) ) ),
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
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_zfmisc_1 @ X23 @ X24 )
        = k1_xboole_0 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('29',plain,(
    ! [X23: $i] :
      ( ( k2_zfmisc_1 @ X23 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['13','34'])).

thf('36',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ X32 )
      | ( ( sk_B @ X32 )
       != ( k4_tarski @ X34 @ X33 ) ) ) ),
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
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('42',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('44',plain,(
    $false ),
    inference('sup-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.buKjQXbK85
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 64 iterations in 0.027s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.47  thf(d1_tarski, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.47         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.47  thf('1', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.47  thf(t20_mcart_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.47       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.47          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.47      inference('split', [status(esa)], ['2'])).
% 0.19/0.47  thf('4', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('5', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C_1))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X29 : $i, X30 : $i]: ((k1_mcart_1 @ (k4_tarski @ X29 @ X30)) = (X29))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('7', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.19/0.48  thf('9', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_1))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X29 : $i, X31 : $i]: ((k2_mcart_1 @ (k4_tarski @ X29 @ X31)) = (X31))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('11', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.19/0.48      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.19/0.48         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['3', '12'])).
% 0.19/0.48  thf('14', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['8', '11'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.19/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf(t9_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.48                 ( ![C:$i,D:$i]:
% 0.19/0.48                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.48                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.48         (((X32) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X33 @ X32)
% 0.19/0.48          | ((sk_B @ X32) != (k4_tarski @ X34 @ X33)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      ((![X0 : $i]:
% 0.19/0.48          (((sk_B @ X0) != (sk_A))
% 0.19/0.48           | ~ (r2_hidden @ sk_A @ X0)
% 0.19/0.48           | ((X0) = (k1_xboole_0))))
% 0.19/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.48         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.19/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X32 : $i]:
% 0.19/0.48         (((X32) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X32) @ X32))),
% 0.19/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X3 : $i]:
% 0.19/0.48         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.19/0.48         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('clc', [status(thm)], ['20', '24'])).
% 0.19/0.48  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf(t113_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X23 : $i, X24 : $i]:
% 0.19/0.48         (((k2_zfmisc_1 @ X23 @ X24) = (k1_xboole_0))
% 0.19/0.48          | ((X24) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X23 : $i]: ((k2_zfmisc_1 @ X23 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.19/0.48  thf(t152_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X25 : $i, X26 : $i]: ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.19/0.48      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.19/0.48  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('split', [status(esa)], ['2'])).
% 0.19/0.48  thf('34', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain, (((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A)))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['13', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.19/0.48         (((X32) = (k1_xboole_0))
% 0.19/0.48          | ~ (r2_hidden @ X34 @ X32)
% 0.19/0.48          | ((sk_B @ X32) != (k4_tarski @ X34 @ X33)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B @ X0) != (sk_A))
% 0.19/0.48          | ~ (r2_hidden @ sk_A @ X0)
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.19/0.48  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.48  thf('41', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.19/0.48  thf('42', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.19/0.48      inference('sup+', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('44', plain, ($false), inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
