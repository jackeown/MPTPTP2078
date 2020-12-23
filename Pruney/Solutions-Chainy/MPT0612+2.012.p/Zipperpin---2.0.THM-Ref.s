%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rgHer8SlBz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:11 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  363 ( 484 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k6_subset_1 @ X19 @ ( k7_relat_1 @ X19 @ X21 ) )
        = ( k7_relat_1 @ X19 @ ( k6_subset_1 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k4_xboole_0 @ X19 @ ( k7_relat_1 @ X19 @ X21 ) )
        = ( k7_relat_1 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X11 @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X16 ) @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C_2 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k6_subset_1 @ X14 @ X15 )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C_2 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rgHer8SlBz
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:22:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 994 iterations in 0.332s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.78  thf(d10_xboole_0, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.79  thf('0', plain,
% 0.60/0.79      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.60/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.79  thf('1', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.60/0.79      inference('simplify', [status(thm)], ['0'])).
% 0.60/0.79  thf(t211_relat_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( v1_relat_1 @ C ) =>
% 0.60/0.79       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.60/0.79         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.60/0.79           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.60/0.79  thf('2', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.79         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.60/0.79          | ((k6_subset_1 @ X19 @ (k7_relat_1 @ X19 @ X21))
% 0.60/0.79              = (k7_relat_1 @ X19 @ (k6_subset_1 @ X20 @ X21)))
% 0.60/0.79          | ~ (v1_relat_1 @ X19))),
% 0.60/0.79      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.60/0.79  thf(redefinition_k6_subset_1, axiom,
% 0.60/0.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.60/0.79  thf('3', plain,
% 0.60/0.79      (![X14 : $i, X15 : $i]:
% 0.60/0.79         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.79  thf('4', plain,
% 0.60/0.79      (![X14 : $i, X15 : $i]:
% 0.60/0.79         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.79  thf('5', plain,
% 0.60/0.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.79         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.60/0.79          | ((k4_xboole_0 @ X19 @ (k7_relat_1 @ X19 @ X21))
% 0.60/0.79              = (k7_relat_1 @ X19 @ (k4_xboole_0 @ X20 @ X21)))
% 0.60/0.79          | ~ (v1_relat_1 @ X19))),
% 0.60/0.79      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.60/0.79  thf('6', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X0)
% 0.60/0.79          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.60/0.79              = (k7_relat_1 @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ X0) @ X1))))),
% 0.60/0.79      inference('sup-', [status(thm)], ['1', '5'])).
% 0.60/0.79  thf('7', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.60/0.79      inference('simplify', [status(thm)], ['0'])).
% 0.60/0.79  thf(t106_xboole_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.60/0.79       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.60/0.79  thf('8', plain,
% 0.60/0.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X11 @ X13)
% 0.60/0.79          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X13)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.60/0.79  thf('9', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.60/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.79  thf(t3_xboole_0, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.60/0.79            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.79       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.79            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.60/0.79  thf('10', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf(t216_relat_1, conjecture,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( v1_relat_1 @ C ) =>
% 0.60/0.79       ( ( r1_tarski @ A @ B ) =>
% 0.60/0.79         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.60/0.79           ( k1_xboole_0 ) ) ) ))).
% 0.60/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.79        ( ( v1_relat_1 @ C ) =>
% 0.60/0.79          ( ( r1_tarski @ A @ B ) =>
% 0.60/0.79            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.60/0.79              ( k1_xboole_0 ) ) ) ) )),
% 0.60/0.79    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.60/0.79  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf(d3_tarski, axiom,
% 0.60/0.79    (![A:$i,B:$i]:
% 0.60/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.79  thf('12', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.79          | (r2_hidden @ X0 @ X2)
% 0.60/0.79          | ~ (r1_tarski @ X1 @ X2))),
% 0.60/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.79  thf('13', plain,
% 0.60/0.79      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.79  thf('14', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X0 @ sk_A) | (r2_hidden @ (sk_C_1 @ sk_A @ X0) @ sk_B))),
% 0.60/0.79      inference('sup-', [status(thm)], ['10', '13'])).
% 0.60/0.79  thf('15', plain,
% 0.60/0.79      (![X4 : $i, X5 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('16', plain,
% 0.60/0.79      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.60/0.79         (~ (r2_hidden @ X6 @ X4)
% 0.60/0.79          | ~ (r2_hidden @ X6 @ X7)
% 0.60/0.79          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.60/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.60/0.79  thf('17', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X0 @ X1)
% 0.60/0.79          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.60/0.79          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.60/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.79  thf('18', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         ((r1_xboole_0 @ X0 @ sk_A)
% 0.60/0.79          | ~ (r1_xboole_0 @ X0 @ sk_B)
% 0.60/0.79          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.60/0.79      inference('sup-', [status(thm)], ['14', '17'])).
% 0.60/0.79  thf('19', plain,
% 0.60/0.79      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.60/0.79      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.79  thf('20', plain,
% 0.60/0.79      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.60/0.79      inference('sup-', [status(thm)], ['9', '19'])).
% 0.60/0.79  thf(t207_relat_1, axiom,
% 0.60/0.79    (![A:$i,B:$i,C:$i]:
% 0.60/0.79     ( ( v1_relat_1 @ C ) =>
% 0.60/0.79       ( ( r1_xboole_0 @ A @ B ) =>
% 0.60/0.79         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.79  thf('21', plain,
% 0.60/0.79      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.79         (~ (r1_xboole_0 @ X16 @ X17)
% 0.60/0.79          | ~ (v1_relat_1 @ X18)
% 0.60/0.79          | ((k7_relat_1 @ (k7_relat_1 @ X18 @ X16) @ X17) = (k1_xboole_0)))),
% 0.60/0.79      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.60/0.79  thf('22', plain,
% 0.60/0.79      (![X0 : $i, X1 : $i]:
% 0.60/0.79         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.60/0.79            = (k1_xboole_0))
% 0.60/0.79          | ~ (v1_relat_1 @ X1))),
% 0.60/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.79  thf('23', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.60/0.79            = (k1_xboole_0))
% 0.60/0.79          | ~ (v1_relat_1 @ X0)
% 0.60/0.79          | ~ (v1_relat_1 @ X0))),
% 0.60/0.79      inference('sup+', [status(thm)], ['6', '22'])).
% 0.60/0.79  thf('24', plain,
% 0.60/0.79      (![X0 : $i]:
% 0.60/0.79         (~ (v1_relat_1 @ X0)
% 0.60/0.79          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.60/0.79              = (k1_xboole_0)))),
% 0.60/0.79      inference('simplify', [status(thm)], ['23'])).
% 0.60/0.79  thf('25', plain,
% 0.60/0.79      (((k7_relat_1 @ (k6_subset_1 @ sk_C_2 @ (k7_relat_1 @ sk_C_2 @ sk_B)) @ 
% 0.60/0.79         sk_A) != (k1_xboole_0))),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('26', plain,
% 0.60/0.79      (![X14 : $i, X15 : $i]:
% 0.60/0.79         ((k6_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))),
% 0.60/0.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.60/0.79  thf('27', plain,
% 0.60/0.79      (((k7_relat_1 @ (k4_xboole_0 @ sk_C_2 @ (k7_relat_1 @ sk_C_2 @ sk_B)) @ 
% 0.60/0.79         sk_A) != (k1_xboole_0))),
% 0.60/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.79  thf('28', plain,
% 0.60/0.79      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C_2))),
% 0.60/0.79      inference('sup-', [status(thm)], ['24', '27'])).
% 0.60/0.79  thf('29', plain, ((v1_relat_1 @ sk_C_2)),
% 0.60/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.79  thf('30', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.60/0.79      inference('demod', [status(thm)], ['28', '29'])).
% 0.60/0.79  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.60/0.79  
% 0.60/0.79  % SZS output end Refutation
% 0.60/0.79  
% 0.60/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
