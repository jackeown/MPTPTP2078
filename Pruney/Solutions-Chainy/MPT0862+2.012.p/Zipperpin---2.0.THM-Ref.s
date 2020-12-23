%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R6NmR71RsP

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  94 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  325 (1013 expanded)
%              Number of equality atoms :   59 ( 165 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X7 ) @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_tarski @ ( k4_tarski @ X7 @ X8 ) @ ( k4_tarski @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X3
        = ( k4_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k4_tarski @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D_1 ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('6',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X11 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('7',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i,X13: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X11 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('9',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D_1 ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_B != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('23',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D_1 ),
    inference(simpl_trail,[status(thm)],['11','23'])).

thf('25',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['18'])).

thf('26',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('27',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['21','26'])).

thf('28',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','24','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R6NmR71RsP
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 63 iterations in 0.041s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.50  thf(t18_mcart_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @
% 0.22/0.50         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.50       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.50         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ( r2_hidden @
% 0.22/0.50            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.50          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.50            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((r2_hidden @ sk_A @ 
% 0.22/0.50        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t36_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.22/0.50         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.22/0.50       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.22/0.50         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((k2_zfmisc_1 @ (k1_tarski @ X7) @ (k2_tarski @ X8 @ X9))
% 0.22/0.50           = (k2_tarski @ (k4_tarski @ X7 @ X8) @ (k4_tarski @ X7 @ X9)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.22/0.50  thf(d2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.50          | ((X4) = (X3))
% 0.22/0.50          | ((X4) = (X0))
% 0.22/0.50          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         (((X4) = (X0))
% 0.22/0.50          | ((X4) = (X3))
% 0.22/0.50          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X3 @ 
% 0.22/0.50             (k2_zfmisc_1 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))
% 0.22/0.50          | ((X3) = (k4_tarski @ X2 @ X1))
% 0.22/0.50          | ((X3) = (k4_tarski @ X2 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((((sk_A) = (k4_tarski @ sk_B @ sk_D_1))
% 0.22/0.50        | ((sk_A) = (k4_tarski @ sk_B @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.50  thf(t7_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X11 : $i, X13 : $i]: ((k2_mcart_1 @ (k4_tarski @ X11 @ X13)) = (X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((((k2_mcart_1 @ sk_A) = (sk_D_1)) | ((sk_A) = (k4_tarski @ sk_B @ sk_C)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X11 : $i, X13 : $i]: ((k2_mcart_1 @ (k4_tarski @ X11 @ X13)) = (X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.22/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.50      inference('split', [status(esa)], ['10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((((sk_A) = (k4_tarski @ sk_B @ sk_D_1))
% 0.22/0.50        | ((sk_A) = (k4_tarski @ sk_B @ sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '4'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]: ((k1_mcart_1 @ (k4_tarski @ X11 @ X12)) = (X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((sk_A) = (k4_tarski @ sk_B @ sk_C)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]: ((k1_mcart_1 @ (k4_tarski @ X11 @ X12)) = (X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.22/0.50      inference('simplify', [status(thm)], ['16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.22/0.50         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((sk_B) != (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '19'])).
% 0.22/0.50  thf('21', plain, ((((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) | 
% 0.22/0.50       ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['10'])).
% 0.22/0.50  thf('23', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, (((k2_mcart_1 @ sk_A) != (sk_D_1))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['11', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.22/0.50         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (~ (((k2_mcart_1 @ sk_A) = (sk_C))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('27', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['21', '26'])).
% 0.22/0.50  thf('28', plain, (((k2_mcart_1 @ sk_A) != (sk_C))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.22/0.50  thf('29', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['9', '24', '28'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
