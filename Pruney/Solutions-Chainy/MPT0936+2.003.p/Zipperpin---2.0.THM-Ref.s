%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQDIt1Sjeb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 103 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  455 (1269 expanded)
%              Number of equality atoms :   49 ( 139 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('0',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_mcart_1 @ X20 @ X21 @ X22 )
      = ( k4_tarski @ ( k4_tarski @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
        = X0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('4',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_D_1 @ X17 @ X15 ) ) @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 )
        = X1 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( sk_D_1 @ ( sk_C @ ( k1_relat_1 @ X0 ) @ X1 ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X6 ) @ ( k1_tarski @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X12 ) )
      = ( k1_tarski @ ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 = X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k1_tarski @ ( k4_tarski @ X6 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
        = X2 )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) @ X2 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X2 )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) @ X0 )
        = X2 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) @ X2 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('13',plain,(
    ! [X0: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X4 @ X0 )
       != X0 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X0 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ X0 )
       != X0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 )
      | ( r2_hidden @ X13 @ X16 )
      | ( X16
       != ( k1_relat_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X15 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ X0 )
       != X0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) @ X0 )
       != X0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
      = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('26',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZQDIt1Sjeb
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.05/1.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.25  % Solved by: fo/fo7.sh
% 1.05/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.25  % done 721 iterations in 0.798s
% 1.05/1.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.25  % SZS output start Refutation
% 1.05/1.25  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.05/1.25  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.05/1.25  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.05/1.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.25  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.05/1.25  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.05/1.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.05/1.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.05/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.05/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.25  thf(t97_mcart_1, conjecture,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( k1_relat_1 @
% 1.05/1.25         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 1.05/1.25       ( k1_tarski @ A ) ))).
% 1.05/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.25    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.25        ( ( k1_relat_1 @
% 1.05/1.25            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 1.05/1.25          ( k1_tarski @ A ) ) )),
% 1.05/1.25    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 1.05/1.25  thf('0', plain,
% 1.05/1.25      (((k1_relat_1 @ 
% 1.05/1.25         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_2))))
% 1.05/1.25         != (k1_tarski @ sk_A))),
% 1.05/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.25  thf(d3_mcart_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i]:
% 1.05/1.25     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.05/1.25  thf('1', plain,
% 1.05/1.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.05/1.25         ((k3_mcart_1 @ X20 @ X21 @ X22)
% 1.05/1.25           = (k4_tarski @ (k4_tarski @ X20 @ X21) @ X22))),
% 1.05/1.25      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.05/1.25  thf(d1_tarski, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.05/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.05/1.25  thf('2', plain,
% 1.05/1.25      (![X0 : $i, X4 : $i]:
% 1.05/1.25         (((X4) = (k1_tarski @ X0))
% 1.05/1.25          | ((sk_C @ X4 @ X0) = (X0))
% 1.05/1.25          | (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [d1_tarski])).
% 1.05/1.25  thf(d4_relat_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.05/1.25       ( ![C:$i]:
% 1.05/1.25         ( ( r2_hidden @ C @ B ) <=>
% 1.05/1.25           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.05/1.25  thf('3', plain,
% 1.05/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X17 @ X16)
% 1.05/1.25          | (r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 1.05/1.25          | ((X16) != (k1_relat_1 @ X15)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.05/1.25  thf('4', plain,
% 1.05/1.25      (![X15 : $i, X17 : $i]:
% 1.05/1.25         ((r2_hidden @ (k4_tarski @ X17 @ (sk_D_1 @ X17 @ X15)) @ X15)
% 1.05/1.25          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X15)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['3'])).
% 1.05/1.25  thf('5', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((sk_C @ (k1_relat_1 @ X0) @ X1) = (X1))
% 1.05/1.25          | ((k1_relat_1 @ X0) = (k1_tarski @ X1))
% 1.05/1.25          | (r2_hidden @ 
% 1.05/1.25             (k4_tarski @ (sk_C @ (k1_relat_1 @ X0) @ X1) @ 
% 1.05/1.25              (sk_D_1 @ (sk_C @ (k1_relat_1 @ X0) @ X1) @ X0)) @ 
% 1.05/1.25             X0))),
% 1.05/1.25      inference('sup-', [status(thm)], ['2', '4'])).
% 1.05/1.25  thf(t34_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.25     ( ( r2_hidden @
% 1.05/1.25         ( k4_tarski @ A @ B ) @ 
% 1.05/1.25         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 1.05/1.25       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 1.05/1.25  thf('6', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.25         (((X7) = (X6))
% 1.05/1.25          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 1.05/1.25               (k2_zfmisc_1 @ (k1_tarski @ X6) @ (k1_tarski @ X9))))),
% 1.05/1.25      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 1.05/1.25  thf(t35_zfmisc_1, axiom,
% 1.05/1.25    (![A:$i,B:$i]:
% 1.05/1.25     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.05/1.25       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 1.05/1.25  thf('7', plain,
% 1.05/1.25      (![X11 : $i, X12 : $i]:
% 1.05/1.25         ((k2_zfmisc_1 @ (k1_tarski @ X11) @ (k1_tarski @ X12))
% 1.05/1.25           = (k1_tarski @ (k4_tarski @ X11 @ X12)))),
% 1.05/1.25      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 1.05/1.25  thf('8', plain,
% 1.05/1.25      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.25         (((X7) = (X6))
% 1.05/1.25          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ 
% 1.05/1.25               (k1_tarski @ (k4_tarski @ X6 @ X9))))),
% 1.05/1.25      inference('demod', [status(thm)], ['6', '7'])).
% 1.05/1.25  thf('9', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 1.05/1.25            = (k1_tarski @ X2))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 1.05/1.25              = (X2))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) @ X2)
% 1.05/1.25              = (X1)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['5', '8'])).
% 1.05/1.25  thf('10', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (((X0) != (X2))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))) @ X0)
% 1.05/1.25              = (X2))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0)))),
% 1.05/1.25      inference('eq_fact', [status(thm)], ['9'])).
% 1.05/1.25  thf('11', plain,
% 1.05/1.25      (![X1 : $i, X2 : $i]:
% 1.05/1.25         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 1.05/1.25            = (k1_tarski @ X2))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))) @ X2)
% 1.05/1.25              = (X2)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['10'])).
% 1.05/1.25  thf('12', plain,
% 1.05/1.25      (![X1 : $i, X2 : $i]:
% 1.05/1.25         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 1.05/1.25            = (k1_tarski @ X2))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1))) @ X2)
% 1.05/1.25              = (X2)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['10'])).
% 1.05/1.25  thf('13', plain,
% 1.05/1.25      (![X0 : $i, X4 : $i]:
% 1.05/1.25         (((X4) = (k1_tarski @ X0))
% 1.05/1.25          | ((sk_C @ X4 @ X0) != (X0))
% 1.05/1.25          | ~ (r2_hidden @ (sk_C @ X4 @ X0) @ X4))),
% 1.05/1.25      inference('cnf', [status(esa)], [d1_tarski])).
% 1.05/1.25  thf('14', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (~ (r2_hidden @ X0 @ 
% 1.05/1.25             (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ X0)
% 1.05/1.25              != (X0))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['12', '13'])).
% 1.05/1.25  thf('15', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d1_tarski])).
% 1.05/1.25  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.05/1.25      inference('simplify', [status(thm)], ['15'])).
% 1.05/1.25  thf('17', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.05/1.25         (~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15)
% 1.05/1.25          | (r2_hidden @ X13 @ X16)
% 1.05/1.25          | ((X16) != (k1_relat_1 @ X15)))),
% 1.05/1.25      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.05/1.25  thf('18', plain,
% 1.05/1.25      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.25         ((r2_hidden @ X13 @ (k1_relat_1 @ X15))
% 1.05/1.25          | ~ (r2_hidden @ (k4_tarski @ X13 @ X14) @ X15))),
% 1.05/1.25      inference('simplify', [status(thm)], ['17'])).
% 1.05/1.25  thf('19', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (r2_hidden @ X1 @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 1.05/1.25      inference('sup-', [status(thm)], ['16', '18'])).
% 1.05/1.25  thf('20', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25            = (k1_tarski @ X0))
% 1.05/1.25          | ((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ X0)
% 1.05/1.25              != (X0))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0)))),
% 1.05/1.25      inference('demod', [status(thm)], ['14', '19'])).
% 1.05/1.25  thf('21', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((sk_C @ (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))) @ X0)
% 1.05/1.25            != (X0))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0)))),
% 1.05/1.25      inference('simplify', [status(thm)], ['20'])).
% 1.05/1.25  thf('22', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         (((X0) != (X0))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0))
% 1.05/1.25          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 1.05/1.25              = (k1_tarski @ X0)))),
% 1.05/1.25      inference('sup-', [status(thm)], ['11', '21'])).
% 1.05/1.25  thf('23', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))) = (k1_tarski @ X0))),
% 1.05/1.25      inference('simplify', [status(thm)], ['22'])).
% 1.05/1.25  thf('24', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.25         ((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 1.05/1.25           = (k1_tarski @ (k4_tarski @ X2 @ X1)))),
% 1.05/1.25      inference('sup+', [status(thm)], ['1', '23'])).
% 1.05/1.25  thf('25', plain,
% 1.05/1.25      (![X0 : $i, X1 : $i]:
% 1.05/1.25         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))) = (k1_tarski @ X0))),
% 1.05/1.25      inference('simplify', [status(thm)], ['22'])).
% 1.05/1.25  thf('26', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 1.05/1.25      inference('demod', [status(thm)], ['0', '24', '25'])).
% 1.05/1.25  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 1.05/1.25  
% 1.05/1.25  % SZS output end Refutation
% 1.05/1.25  
% 1.05/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
