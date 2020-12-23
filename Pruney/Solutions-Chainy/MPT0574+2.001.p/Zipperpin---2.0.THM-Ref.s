%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EU93lNXV0U

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:16 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  425 ( 669 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X13: $i] :
      ( ( X11 = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('26',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','37'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k10_relat_1 @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X28 @ X29 ) @ ( k10_relat_1 @ X28 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EU93lNXV0U
% 0.13/0.36  % Computer   : n012.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:01:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.68/0.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.87  % Solved by: fo/fo7.sh
% 0.68/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.87  % done 1103 iterations in 0.406s
% 0.68/0.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.87  % SZS output start Refutation
% 0.68/0.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.87  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.87  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.68/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.68/0.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.87  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.87  thf(d3_tarski, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.87  thf('0', plain,
% 0.68/0.87      (![X1 : $i, X3 : $i]:
% 0.68/0.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.87  thf(t178_relat_1, conjecture,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( v1_relat_1 @ C ) =>
% 0.68/0.87       ( ( r1_tarski @ A @ B ) =>
% 0.68/0.87         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.87    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.87        ( ( v1_relat_1 @ C ) =>
% 0.68/0.87          ( ( r1_tarski @ A @ B ) =>
% 0.68/0.87            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.68/0.87    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.68/0.87  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.68/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.87  thf('2', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.87          | (r2_hidden @ X0 @ X2)
% 0.68/0.87          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.87  thf('3', plain,
% 0.68/0.87      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.68/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.87  thf('4', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.68/0.87      inference('sup-', [status(thm)], ['0', '3'])).
% 0.68/0.87  thf(t7_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('5', plain,
% 0.68/0.87      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.68/0.87      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.87  thf('6', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.87          | (r2_hidden @ X0 @ X2)
% 0.68/0.87          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.87  thf('7', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.87         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.87      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.87  thf('8', plain,
% 0.68/0.87      (![X0 : $i, X1 : $i]:
% 0.68/0.87         ((r1_tarski @ sk_A @ X0)
% 0.68/0.87          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_xboole_0 @ sk_B @ X1)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['4', '7'])).
% 0.68/0.87  thf('9', plain,
% 0.68/0.87      (![X1 : $i, X3 : $i]:
% 0.68/0.87         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.87      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.87  thf('10', plain,
% 0.68/0.87      (![X0 : $i]:
% 0.68/0.87         ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.68/0.87          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.87  thf('11', plain,
% 0.68/0.87      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.68/0.87      inference('simplify', [status(thm)], ['10'])).
% 0.68/0.87  thf(t43_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i,C:$i]:
% 0.68/0.87     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.68/0.87       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.68/0.87  thf('12', plain,
% 0.68/0.87      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.68/0.87         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.68/0.87          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.68/0.87      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.68/0.87  thf('13', plain,
% 0.68/0.87      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.68/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.87  thf('14', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.68/0.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.87  thf(d10_xboole_0, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.87  thf('15', plain,
% 0.68/0.87      (![X11 : $i, X13 : $i]:
% 0.68/0.87         (((X11) = (X13))
% 0.68/0.87          | ~ (r1_tarski @ X13 @ X11)
% 0.68/0.87          | ~ (r1_tarski @ X11 @ X13))),
% 0.68/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.87  thf('16', plain,
% 0.68/0.87      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.87      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.87  thf('17', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.68/0.87      inference('sup-', [status(thm)], ['13', '16'])).
% 0.68/0.87  thf(t39_xboole_1, axiom,
% 0.68/0.87    (![A:$i,B:$i]:
% 0.68/0.87     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.87  thf('18', plain,
% 0.68/0.87      (![X15 : $i, X16 : $i]:
% 0.68/0.87         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.68/0.87           = (k2_xboole_0 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup+', [status(thm)], ['17', '18'])).
% 0.68/0.88  thf(commutativity_k2_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X22 : $i, X23 : $i]:
% 0.68/0.88         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 0.68/0.88      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.68/0.88  thf(l51_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X26 : $i, X27 : $i]:
% 0.68/0.88         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (((k2_xboole_0 @ k1_xboole_0 @ sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.68/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.68/0.88         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 0.68/0.88          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '28'])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]:
% 0.68/0.88         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.68/0.88           = (k2_xboole_0 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['31', '32'])).
% 0.68/0.88  thf(idempotence_k2_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.68/0.88  thf('34', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.68/0.88  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['33', '34'])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['22', '23'])).
% 0.68/0.88  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['35', '36'])).
% 0.68/0.88  thf('38', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.68/0.88      inference('demod', [status(thm)], ['26', '37'])).
% 0.68/0.88  thf(t175_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.68/0.88         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.88         (((k10_relat_1 @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 0.68/0.88            = (k2_xboole_0 @ (k10_relat_1 @ X28 @ X29) @ 
% 0.68/0.88               (k10_relat_1 @ X28 @ X30)))
% 0.68/0.88          | ~ (v1_relat_1 @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 0.68/0.88      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.68/0.88           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.68/0.88          | ~ (v1_relat_1 @ X2))),
% 0.68/0.88      inference('sup+', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['38', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (~ (r1_tarski @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.68/0.88          (k10_relat_1 @ sk_C_1 @ sk_B))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('44', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('46', plain, ($false), inference('demod', [status(thm)], ['44', '45'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
