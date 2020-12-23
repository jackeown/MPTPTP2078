%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUlRWVdem0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  80 expanded)
%              Number of leaves         :   16 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  324 ( 829 expanded)
%              Number of equality atoms :   42 ( 116 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( k2_mcart_1 @ A )
          = C ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ X4 ) @ ( k2_zfmisc_1 @ X3 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_mcart_1 @ X12 )
        = X15 )
      | ( ( k2_mcart_1 @ X12 )
        = X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ ( k2_tarski @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('8',plain,
    ( ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_B )
    | ( ( k2_mcart_1 @ ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k1_mcart_1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X16: $i,X18: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X16 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_mcart_1 @ X9 )
        = X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_mcart_1])).

thf('16',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['12'])).

thf('22',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['13','22'])).

thf('24',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('26',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['20','25'])).

thf('27',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['24','26'])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['11','23','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cUlRWVdem0
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 24 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.46  thf(t17_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( r2_hidden @
% 0.21/0.46         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.46       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.46         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46        ( ( r2_hidden @
% 0.21/0.46            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.46          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.46            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((r2_hidden @ sk_A @ 
% 0.21/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t13_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k1_tarski @ C ) ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.46         ( ( k2_mcart_1 @ A ) = ( C ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.21/0.46          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ (k1_tarski @ X11))))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(l54_zfmisc_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.46       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.46         ((r2_hidden @ (k4_tarski @ X2 @ X4) @ (k2_zfmisc_1 @ X3 @ X6))
% 0.21/0.46          | ~ (r2_hidden @ X4 @ X6)
% 0.21/0.46          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.46          | (r2_hidden @ (k4_tarski @ X1 @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.46             (k2_zfmisc_1 @ X0 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((r2_hidden @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)) @ 
% 0.21/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_B @ sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.46  thf(t16_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.21/0.46       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.46         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.46         (((k2_mcart_1 @ X12) = (X15))
% 0.21/0.46          | ((k2_mcart_1 @ X12) = (X14))
% 0.21/0.46          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ (k2_tarski @ X14 @ X15))))),
% 0.21/0.46      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      ((((k2_mcart_1 @ (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A)))
% 0.21/0.46          = (sk_B))
% 0.21/0.46        | ((k2_mcart_1 @ 
% 0.21/0.46            (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k1_mcart_1 @ sk_A))) = (
% 0.21/0.46            sk_C)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(t7_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X16 : $i, X18 : $i]: ((k2_mcart_1 @ (k4_tarski @ X16 @ X18)) = (X18))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.46         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.46      inference('split', [status(esa)], ['12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      ((r2_hidden @ sk_A @ 
% 0.21/0.46        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (((k2_mcart_1 @ X9) = (X11))
% 0.21/0.46          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ (k1_tarski @ X11))))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_mcart_1])).
% 0.21/0.46  thf('16', plain, (((k2_mcart_1 @ sk_A) = (sk_D))),
% 0.21/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.46         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.46      inference('split', [status(esa)], ['17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.46  thf('20', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.46      inference('split', [status(esa)], ['12'])).
% 0.21/0.46  thf('22', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['13', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['17'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['17'])).
% 0.21/0.47  thf('26', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['20', '25'])).
% 0.21/0.47  thf('27', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['24', '26'])).
% 0.21/0.47  thf('28', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['11', '23', '27'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
