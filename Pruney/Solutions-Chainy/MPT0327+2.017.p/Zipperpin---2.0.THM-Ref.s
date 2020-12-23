%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rf8vysKbzp

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 121 expanded)
%              Number of leaves         :   25 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  499 ( 830 expanded)
%              Number of equality atoms :   46 (  78 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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

thf(t140_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t140_zfmisc_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X55 @ X57 ) @ X58 )
      | ~ ( r2_hidden @ X57 @ X58 )
      | ~ ( r2_hidden @ X55 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('26',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ k1_xboole_0 )
      = X31 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ k1_xboole_0 )
      = X31 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ k1_xboole_0 )
      = X31 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','46'])).

thf('48',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_xboole_0 @ X29 @ ( k4_xboole_0 @ X30 @ X29 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('53',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rf8vysKbzp
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 78 iterations in 0.037s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X3 : $i, X5 : $i]:
% 0.22/0.50         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf(t140_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.50       ( ( k2_xboole_0 @
% 0.22/0.50           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.50         ( B ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ( r2_hidden @ A @ B ) =>
% 0.22/0.50          ( ( k2_xboole_0 @
% 0.22/0.50              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 0.22/0.50            ( B ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 0.22/0.50  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t38_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X55 : $i, X57 : $i, X58 : $i]:
% 0.22/0.50         ((r1_tarski @ (k2_tarski @ X55 @ X57) @ X58)
% 0.22/0.50          | ~ (r2_hidden @ X57 @ X58)
% 0.22/0.50          | ~ (r2_hidden @ X55 @ X58))),
% 0.22/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.50          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.50  thf(t69_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('6', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.22/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.50  thf('7', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t28_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf(t100_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X16 @ X17)
% 0.22/0.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.22/0.50         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.50  thf('12', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X16 @ X17)
% 0.22/0.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf(d5_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.50       ( ![D:$i]:
% 0.22/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.50          | (r2_hidden @ X10 @ X7)
% 0.22/0.50          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.50         ((r2_hidden @ X10 @ X7)
% 0.22/0.50          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.50          | ~ (r2_hidden @ X10 @ X8)
% 0.22/0.50          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X10 @ X8)
% 0.22/0.50          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.50          | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.50      inference('clc', [status(thm)], ['17', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ X0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X3 : $i, X5 : $i]:
% 0.22/0.50         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf(t5_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('26', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ k1_xboole_0) = (X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.50          | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '20'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.50  thf('30', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '29'])).
% 0.22/0.50  thf(d10_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X13 : $i, X15 : $i]:
% 0.22/0.50         (((X13) = (X15))
% 0.22/0.50          | ~ (r1_tarski @ X15 @ X13)
% 0.22/0.50          | ~ (r1_tarski @ X13 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '32'])).
% 0.22/0.50  thf(t39_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X29 : $i, X30 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 0.22/0.50           = (k2_xboole_0 @ X29 @ X30))),
% 0.22/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.22/0.50         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '29'])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X27 : $i, X28 : $i]:
% 0.22/0.50         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.22/0.50      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X16 @ X17)
% 0.22/0.50           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.22/0.50           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('41', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ k1_xboole_0) = (X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf(t98_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (![X32 : $i, X33 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X32 @ X33)
% 0.22/0.50           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.50  thf('45', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ k1_xboole_0) = (X31))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.50  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.50  thf('47', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.22/0.50         (k1_tarski @ sk_A)) != (sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.22/0.50         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X29 : $i, X30 : $i]:
% 0.22/0.50         ((k2_xboole_0 @ X29 @ (k4_xboole_0 @ X30 @ X29))
% 0.22/0.50           = (k2_xboole_0 @ X29 @ X30))),
% 0.22/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.50  thf('53', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.50  thf('54', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['47', '53'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
