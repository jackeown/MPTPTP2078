%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMLrNnBt08

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:29 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :   48 (  58 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  342 ( 436 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X8
       != ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('2',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_xboole_0 @ X9 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMLrNnBt08
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.66/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.89  % Solved by: fo/fo7.sh
% 0.66/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.89  % done 715 iterations in 0.427s
% 0.66/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.89  % SZS output start Refutation
% 0.66/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.66/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.66/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.89  thf(d3_tarski, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.89  thf('0', plain,
% 0.66/0.89      (![X3 : $i, X5 : $i]:
% 0.66/0.89         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.89  thf(d3_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.66/0.89       ( ![D:$i]:
% 0.66/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.66/0.89           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.66/0.89  thf('1', plain,
% 0.66/0.89      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.66/0.89         (~ (r2_hidden @ X10 @ X8)
% 0.66/0.89          | (r2_hidden @ X10 @ X9)
% 0.66/0.89          | (r2_hidden @ X10 @ X7)
% 0.66/0.89          | ((X8) != (k2_xboole_0 @ X9 @ X7)))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.66/0.89  thf('2', plain,
% 0.66/0.89      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.66/0.89         ((r2_hidden @ X10 @ X7)
% 0.66/0.89          | (r2_hidden @ X10 @ X9)
% 0.66/0.89          | ~ (r2_hidden @ X10 @ (k2_xboole_0 @ X9 @ X7)))),
% 0.66/0.89      inference('simplify', [status(thm)], ['1'])).
% 0.66/0.89  thf('3', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         ((r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.66/0.89          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 0.66/0.89          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['0', '2'])).
% 0.66/0.89  thf('4', plain,
% 0.66/0.89      (![X3 : $i, X5 : $i]:
% 0.66/0.89         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.89  thf('5', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1)
% 0.66/0.89          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.66/0.89          | (r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.89  thf('6', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.66/0.89          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ X1)) @ X1))),
% 0.66/0.89      inference('simplify', [status(thm)], ['5'])).
% 0.66/0.89  thf(t156_relat_1, conjecture,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ C ) =>
% 0.66/0.89       ( ( r1_tarski @ A @ B ) =>
% 0.66/0.89         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.89        ( ( v1_relat_1 @ C ) =>
% 0.66/0.89          ( ( r1_tarski @ A @ B ) =>
% 0.66/0.89            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.66/0.89    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.66/0.89  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('8', plain,
% 0.66/0.89      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.66/0.89         (~ (r2_hidden @ X2 @ X3)
% 0.66/0.89          | (r2_hidden @ X2 @ X4)
% 0.66/0.89          | ~ (r1_tarski @ X3 @ X4))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.89  thf('9', plain,
% 0.66/0.89      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.66/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.66/0.89  thf('10', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((r1_tarski @ (k2_xboole_0 @ X0 @ sk_A) @ X0)
% 0.66/0.89          | (r2_hidden @ (sk_C @ X0 @ (k2_xboole_0 @ X0 @ sk_A)) @ sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['6', '9'])).
% 0.66/0.89  thf('11', plain,
% 0.66/0.89      (![X3 : $i, X5 : $i]:
% 0.66/0.89         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.66/0.89      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.89  thf('12', plain,
% 0.66/0.89      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B)
% 0.66/0.89        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_A) @ sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.66/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.66/0.89  thf('13', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.66/0.89  thf('14', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.66/0.89  thf('15', plain,
% 0.66/0.89      (((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.66/0.89        | (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.66/0.89      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.66/0.89  thf('16', plain, ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.66/0.89      inference('simplify', [status(thm)], ['15'])).
% 0.66/0.89  thf('17', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.66/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.66/0.89  thf(t7_xboole_1, axiom,
% 0.66/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.89  thf('18', plain,
% 0.66/0.89      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.66/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.89  thf('19', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['17', '18'])).
% 0.66/0.89  thf(d10_xboole_0, axiom,
% 0.66/0.89    (![A:$i,B:$i]:
% 0.66/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.89  thf('20', plain,
% 0.66/0.89      (![X12 : $i, X14 : $i]:
% 0.66/0.89         (((X12) = (X14))
% 0.66/0.89          | ~ (r1_tarski @ X14 @ X12)
% 0.66/0.89          | ~ (r1_tarski @ X12 @ X14))),
% 0.66/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.89  thf('21', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i]:
% 0.66/0.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.89          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.66/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.66/0.89  thf('22', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.66/0.89      inference('sup-', [status(thm)], ['16', '21'])).
% 0.66/0.89  thf(t153_relat_1, axiom,
% 0.66/0.89    (![A:$i,B:$i,C:$i]:
% 0.66/0.89     ( ( v1_relat_1 @ C ) =>
% 0.66/0.89       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.66/0.89         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.66/0.89  thf('23', plain,
% 0.66/0.89      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.66/0.89         (((k9_relat_1 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.66/0.89            = (k2_xboole_0 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.66/0.89               (k9_relat_1 @ X17 @ X19)))
% 0.66/0.89          | ~ (v1_relat_1 @ X17))),
% 0.66/0.89      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.66/0.89  thf('24', plain,
% 0.66/0.89      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.66/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.89  thf('25', plain,
% 0.66/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.89         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 0.66/0.89           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.66/0.89          | ~ (v1_relat_1 @ X2))),
% 0.66/0.89      inference('sup+', [status(thm)], ['23', '24'])).
% 0.66/0.89  thf('26', plain,
% 0.66/0.89      (![X0 : $i]:
% 0.66/0.89         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.66/0.89          | ~ (v1_relat_1 @ X0))),
% 0.66/0.89      inference('sup+', [status(thm)], ['22', '25'])).
% 0.66/0.89  thf('27', plain,
% 0.66/0.89      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.66/0.89          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('28', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.66/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.66/0.89  thf('29', plain, ((v1_relat_1 @ sk_C_1)),
% 0.66/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.89  thf('30', plain, ($false), inference('demod', [status(thm)], ['28', '29'])).
% 0.66/0.89  
% 0.66/0.89  % SZS output end Refutation
% 0.66/0.89  
% 0.66/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
