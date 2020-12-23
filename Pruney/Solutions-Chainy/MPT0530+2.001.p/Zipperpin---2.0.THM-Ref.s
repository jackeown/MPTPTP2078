%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5EndxHgopt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 105 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  425 ( 788 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k8_relat_1 @ X26 @ ( k8_relat_1 @ X27 @ X28 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X26 @ X27 ) @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t130_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_relat_1])).

thf('1',plain,(
    ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C_2 ) )
 != ( k8_relat_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 )
     != ( k8_relat_1 @ sk_A @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C_2 )
 != ( k8_relat_1 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_A @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ( k8_relat_1 @ sk_A @ sk_C_2 )
 != ( k8_relat_1 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['4','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5EndxHgopt
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:58:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 346 iterations in 0.131s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(t127_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ C ) =>
% 0.21/0.60       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.21/0.60         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.60         (((k8_relat_1 @ X26 @ (k8_relat_1 @ X27 @ X28))
% 0.21/0.60            = (k8_relat_1 @ (k3_xboole_0 @ X26 @ X27) @ X28))
% 0.21/0.60          | ~ (v1_relat_1 @ X28))),
% 0.21/0.60      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.21/0.60  thf(t130_relat_1, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ C ) =>
% 0.21/0.60       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.60         ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.60        ( ( v1_relat_1 @ C ) =>
% 0.21/0.60          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.60            ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.21/0.60              ( k8_relat_1 @ A @ C ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t130_relat_1])).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C_2))
% 0.21/0.60         != (k8_relat_1 @ sk_A @ sk_C_2))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C_2)
% 0.21/0.60          != (k8_relat_1 @ sk_A @ sk_C_2))
% 0.21/0.60        | ~ (v1_relat_1 @ sk_C_2))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.60  thf('3', plain, ((v1_relat_1 @ sk_C_2)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C_2)
% 0.21/0.60         != (k8_relat_1 @ sk_A @ sk_C_2))),
% 0.21/0.60      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf(d3_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X1 : $i, X3 : $i]:
% 0.21/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf(d5_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.60       ( ![D:$i]:
% 0.21/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.60          | (r2_hidden @ X8 @ X5)
% 0.21/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.60         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.60  thf('8', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.60          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.60  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.60          | (r2_hidden @ X0 @ X2)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ X1)
% 0.21/0.60          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_A @ X0)) @ sk_B))),
% 0.21/0.60      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X1 : $i, X3 : $i]:
% 0.21/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.60          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.60          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.60          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.60          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.21/0.60          | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['12', '16'])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.21/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (![X1 : $i, X3 : $i]:
% 0.21/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.60  thf('20', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.60  thf(t48_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.60           = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.60          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.60          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.60         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.60      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['19', '26'])).
% 0.21/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.60  thf('28', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.21/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.60  thf(d10_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X13 : $i, X15 : $i]:
% 0.21/0.60         (((X13) = (X15))
% 0.21/0.60          | ~ (r1_tarski @ X15 @ X13)
% 0.21/0.60          | ~ (r1_tarski @ X13 @ X15))),
% 0.21/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf('34', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '33'])).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.60           = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.60  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]:
% 0.21/0.60         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.21/0.60           = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf('40', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.60  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('42', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.60      inference('demod', [status(thm)], ['36', '41'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (((k8_relat_1 @ sk_A @ sk_C_2) != (k8_relat_1 @ sk_A @ sk_C_2))),
% 0.21/0.60      inference('demod', [status(thm)], ['4', '42'])).
% 0.21/0.60  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
