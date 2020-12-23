%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZMn9zl6Ag

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:23 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 120 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  473 (1395 expanded)
%              Number of equality atoms :   49 ( 169 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_tarski @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ ( sk_D @ X1 @ ( k1_tarski @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ X0 )
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( X1
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ X1 ) ) )
      | ( ( k1_mcart_1 @ X1 )
        = ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_mcart_1 @ X0 )
       != X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( ( k1_tarski @ X1 )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_mcart_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = ( k1_mcart_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('16',plain,(
    ! [X13: $i,X16: $i,X17: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ X17 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ X0 ) @ ( k1_tarski @ ( k1_mcart_1 @ X0 ) ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ X0 ) )
        = ( k1_relat_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ ( k1_mcart_1 @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      | ( ( k1_tarski @ X0 )
        = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
      = ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ X1 )
      = ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('29',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LZMn9zl6Ag
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 155 iterations in 0.158s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.43/0.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.43/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.61  thf(t97_mcart_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k1_relat_1 @
% 0.43/0.61         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.43/0.61       ( k1_tarski @ A ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.61        ( ( k1_relat_1 @
% 0.43/0.61            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.43/0.61          ( k1_tarski @ A ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      (((k1_relat_1 @ 
% 0.43/0.61         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C_2))))
% 0.43/0.61         != (k1_tarski @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d3_mcart_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.61         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 0.43/0.61           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.43/0.61      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.43/0.61  thf(d1_tarski, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.61  thf('3', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.43/0.61  thf(t7_mcart_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.43/0.61       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.43/0.61  thf(d4_relat_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.43/0.61       ( ![C:$i]:
% 0.43/0.61         ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.61           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (![X13 : $i, X16 : $i]:
% 0.43/0.61         (((X16) = (k1_relat_1 @ X13))
% 0.43/0.61          | (r2_hidden @ 
% 0.43/0.61             (k4_tarski @ (sk_C_1 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 0.43/0.61          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (![X0 : $i, X3 : $i]:
% 0.43/0.61         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.43/0.61          | ((X1) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ((k4_tarski @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ 
% 0.43/0.61              (sk_D @ X1 @ (k1_tarski @ X0))) = (X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_mcart_1 @ X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ((X1) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | (r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      (![X0 : $i, X3 : $i]:
% 0.43/0.61         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_tarski @ X0) = (k1_relat_1 @ (k1_tarski @ X1)))
% 0.43/0.61          | ((k1_mcart_1 @ X1) = (sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))
% 0.43/0.61          | ((sk_C_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_mcart_1 @ X0) != (X1))
% 0.43/0.61          | ((sk_C_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) = (X1))
% 0.43/0.61          | ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ X0))))),
% 0.43/0.61      inference('eq_fact', [status(thm)], ['12'])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ((sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ X0)) @ (k1_tarski @ X0))
% 0.43/0.61              = (k1_mcart_1 @ X0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ((sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ X0)) @ (k1_tarski @ X0))
% 0.43/0.61              = (k1_mcart_1 @ X0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.43/0.61  thf('16', plain,
% 0.43/0.61      (![X13 : $i, X16 : $i, X17 : $i]:
% 0.43/0.61         (((X16) = (k1_relat_1 @ X13))
% 0.43/0.61          | ~ (r2_hidden @ (k4_tarski @ (sk_C_1 @ X16 @ X13) @ X17) @ X13)
% 0.43/0.61          | ~ (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.43/0.61      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ X0) @ X1) @ 
% 0.43/0.61             (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ~ (r2_hidden @ 
% 0.43/0.61               (sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ X0)) @ (k1_tarski @ X0)) @ 
% 0.43/0.61               (k1_tarski @ (k1_mcart_1 @ X0)))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ 
% 0.43/0.61             (sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ X0)) @ (k1_tarski @ X0)) @ 
% 0.43/0.61             (k1_tarski @ (k1_mcart_1 @ X0)))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ~ (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ X0) @ X1) @ 
% 0.43/0.61               (k1_tarski @ X0)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k1_mcart_1 @ X0) @ (k1_tarski @ (k1_mcart_1 @ X0)))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ~ (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ X0) @ X1) @ 
% 0.43/0.61               (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '18'])).
% 0.43/0.61  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.43/0.61      inference('simplify', [status(thm)], ['2'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0)))
% 0.43/0.61          | ~ (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ X0) @ X1) @ 
% 0.43/0.61               (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0))))),
% 0.43/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k4_tarski @ (k1_mcart_1 @ X0) @ X1) @ 
% 0.43/0.61             (k1_tarski @ X0))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ X0)) = (k1_relat_1 @ (k1_tarski @ X0))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.43/0.61  thf('23', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 0.43/0.61             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.43/0.61          | ((k1_tarski @ (k1_mcart_1 @ (k4_tarski @ X0 @ X1)))
% 0.43/0.61              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['4', '22'])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]: ((k1_mcart_1 @ (k4_tarski @ X21 @ X22)) = (X21))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         (~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ 
% 0.43/0.61             (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.43/0.61          | ((k1_tarski @ X0)
% 0.43/0.61              = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))),
% 0.43/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '25'])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.61         ((k1_tarski @ (k4_tarski @ X2 @ X1))
% 0.43/0.61           = (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0))))),
% 0.43/0.61      inference('sup+', [status(thm)], ['1', '26'])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k1_tarski @ X1) = (k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['3', '25'])).
% 0.43/0.61  thf('29', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '27', '28'])).
% 0.43/0.61  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
