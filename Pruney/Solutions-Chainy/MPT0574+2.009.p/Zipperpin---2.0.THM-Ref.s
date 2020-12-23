%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mhbDQaSguI

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:17 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   64 (  75 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  376 ( 476 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k2_xboole_0 @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) )
      = ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','24','29'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k10_relat_1 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X25 @ X26 ) @ ( k10_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mhbDQaSguI
% 0.17/0.39  % Computer   : n006.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 09:44:23 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.40  % Python version: Python 3.6.8
% 0.17/0.40  % Running in FO mode
% 0.69/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.87  % Solved by: fo/fo7.sh
% 0.69/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.87  % done 779 iterations in 0.398s
% 0.69/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.87  % SZS output start Refutation
% 0.69/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.69/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.69/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.69/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.87  thf(d3_tarski, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( r1_tarski @ A @ B ) <=>
% 0.69/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.69/0.87  thf('0', plain,
% 0.69/0.87      (![X1 : $i, X3 : $i]:
% 0.69/0.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.69/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.87  thf(t178_relat_1, conjecture,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ C ) =>
% 0.69/0.87       ( ( r1_tarski @ A @ B ) =>
% 0.69/0.87         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.69/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.87        ( ( v1_relat_1 @ C ) =>
% 0.69/0.87          ( ( r1_tarski @ A @ B ) =>
% 0.69/0.87            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.69/0.87    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.69/0.87  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf(idempotence_k2_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.69/0.87  thf('2', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.69/0.87  thf(t43_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.69/0.87       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.69/0.87  thf('3', plain,
% 0.69/0.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.87         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.69/0.87          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.69/0.87      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.69/0.87  thf('4', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         (~ (r1_tarski @ X1 @ X0) | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.87  thf('5', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.69/0.87      inference('sup-', [status(thm)], ['1', '4'])).
% 0.69/0.87  thf('6', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X0 @ X1)
% 0.69/0.87          | (r2_hidden @ X0 @ X2)
% 0.69/0.87          | ~ (r1_tarski @ X1 @ X2))),
% 0.69/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.69/0.87  thf('7', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((r2_hidden @ X0 @ sk_B)
% 0.69/0.87          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.69/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.87  thf(d5_xboole_0, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.87       ( ![D:$i]:
% 0.69/0.87         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.87  thf('8', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X8 @ X7)
% 0.69/0.87          | ~ (r2_hidden @ X8 @ X6)
% 0.69/0.87          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.69/0.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.87  thf('9', plain,
% 0.69/0.87      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.69/0.87         (~ (r2_hidden @ X8 @ X6)
% 0.69/0.87          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.69/0.87      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.87  thf('10', plain,
% 0.69/0.87      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.87      inference('clc', [status(thm)], ['7', '9'])).
% 0.69/0.87  thf('11', plain,
% 0.69/0.87      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['0', '10'])).
% 0.69/0.87  thf(t3_xboole_1, axiom,
% 0.69/0.87    (![A:$i]:
% 0.69/0.87     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.87  thf('12', plain,
% 0.69/0.87      (![X13 : $i]:
% 0.69/0.87         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.69/0.87  thf('13', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.87  thf(t39_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('14', plain,
% 0.69/0.87      (![X11 : $i, X12 : $i]:
% 0.69/0.87         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.69/0.87           = (k2_xboole_0 @ X11 @ X12))),
% 0.69/0.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.69/0.87  thf('15', plain,
% 0.69/0.87      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.69/0.87      inference('sup+', [status(thm)], ['13', '14'])).
% 0.69/0.87  thf(t7_xboole_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('16', plain,
% 0.69/0.87      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.69/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.87  thf('17', plain,
% 0.69/0.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.69/0.87         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.69/0.87          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.69/0.87      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.69/0.87  thf('18', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.69/0.87      inference('sup-', [status(thm)], ['16', '17'])).
% 0.69/0.87  thf('19', plain,
% 0.69/0.87      (![X13 : $i]:
% 0.69/0.87         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.69/0.87      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.69/0.87  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.69/0.87      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.87  thf('21', plain,
% 0.69/0.87      (![X11 : $i, X12 : $i]:
% 0.69/0.87         ((k2_xboole_0 @ X11 @ (k4_xboole_0 @ X12 @ X11))
% 0.69/0.87           = (k2_xboole_0 @ X11 @ X12))),
% 0.69/0.87      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.69/0.87  thf('22', plain,
% 0.69/0.87      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['20', '21'])).
% 0.69/0.87  thf('23', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.69/0.87      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.69/0.87  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.69/0.87      inference('demod', [status(thm)], ['22', '23'])).
% 0.69/0.87  thf(commutativity_k2_tarski, axiom,
% 0.69/0.87    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.69/0.87  thf('25', plain,
% 0.69/0.87      (![X19 : $i, X20 : $i]:
% 0.69/0.87         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.69/0.87      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.69/0.87  thf(l51_zfmisc_1, axiom,
% 0.69/0.87    (![A:$i,B:$i]:
% 0.69/0.87     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.69/0.87  thf('26', plain,
% 0.69/0.87      (![X23 : $i, X24 : $i]:
% 0.69/0.87         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.69/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.87  thf('27', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]:
% 0.69/0.87         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('sup+', [status(thm)], ['25', '26'])).
% 0.69/0.87  thf('28', plain,
% 0.69/0.87      (![X23 : $i, X24 : $i]:
% 0.69/0.87         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 0.69/0.87      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.69/0.87  thf('29', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.69/0.87      inference('sup+', [status(thm)], ['27', '28'])).
% 0.69/0.87  thf('30', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.69/0.87      inference('demod', [status(thm)], ['15', '24', '29'])).
% 0.69/0.87  thf(t175_relat_1, axiom,
% 0.69/0.87    (![A:$i,B:$i,C:$i]:
% 0.69/0.87     ( ( v1_relat_1 @ C ) =>
% 0.69/0.87       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.69/0.87         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.69/0.87  thf('31', plain,
% 0.69/0.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.69/0.87         (((k10_relat_1 @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 0.69/0.87            = (k2_xboole_0 @ (k10_relat_1 @ X25 @ X26) @ 
% 0.69/0.87               (k10_relat_1 @ X25 @ X27)))
% 0.69/0.87          | ~ (v1_relat_1 @ X25))),
% 0.69/0.87      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.69/0.87  thf('32', plain,
% 0.69/0.87      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.69/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.69/0.87  thf('33', plain,
% 0.69/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.87         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.69/0.87           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.69/0.87          | ~ (v1_relat_1 @ X2))),
% 0.69/0.87      inference('sup+', [status(thm)], ['31', '32'])).
% 0.69/0.87  thf('34', plain,
% 0.69/0.87      (![X0 : $i]:
% 0.69/0.87         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.69/0.87          | ~ (v1_relat_1 @ X0))),
% 0.69/0.87      inference('sup+', [status(thm)], ['30', '33'])).
% 0.69/0.87  thf('35', plain,
% 0.69/0.87      (~ (r1_tarski @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.69/0.87          (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('36', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.69/0.87      inference('sup-', [status(thm)], ['34', '35'])).
% 0.69/0.87  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.69/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.87  thf('38', plain, ($false), inference('demod', [status(thm)], ['36', '37'])).
% 0.69/0.87  
% 0.69/0.87  % SZS output end Refutation
% 0.69/0.87  
% 0.72/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
