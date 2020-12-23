%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqN8is7EYW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 187 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  523 (1382 expanded)
%              Number of equality atoms :   58 ( 148 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X46: $i,X48: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X46 ) @ X48 )
      | ~ ( r2_hidden @ X46 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['28','29','30','33','34','37'])).

thf('39',plain,
    ( sk_B
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('47',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['39','47'])).

thf('49',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mqN8is7EYW
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 192 iterations in 0.115s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(t46_zfmisc_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.58       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i]:
% 0.21/0.58        ( ( r2_hidden @ A @ B ) =>
% 0.21/0.58          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.21/0.58  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(l1_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X46 : $i, X48 : $i]:
% 0.21/0.58         ((r1_tarski @ (k1_tarski @ X46) @ X48) | ~ (r2_hidden @ X46 @ X48))),
% 0.21/0.58      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.58  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf(t28_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      (![X8 : $i, X9 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(t94_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k2_xboole_0 @ A @ B ) =
% 0.21/0.58       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.58           = (k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ 
% 0.21/0.58              (k3_xboole_0 @ X16 @ X17)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.21/0.58  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.58           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.21/0.58              (k5_xboole_0 @ X16 @ X17)))),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(t100_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.58  thf(t5_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('15', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.58           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.21/0.58              (k5_xboole_0 @ X16 @ X17)))),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.21/0.58           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['15', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.58  thf(t21_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X4 @ X5)
% 0.21/0.58           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf(t91_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.58       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 0.21/0.58           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0)
% 0.21/0.58           = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.21/0.58           (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.21/0.58           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['23', '26'])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (((k5_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.21/0.58         (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ sk_B @ 
% 0.21/0.58            (k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58             (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))))),
% 0.21/0.58      inference('sup+', [status(thm)], ['22', '27'])).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.58  thf(t46_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('36', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.21/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.58  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['28', '29', '30', '33', '34', '37'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (((sk_B)
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['14', '38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X16 @ X17)
% 0.21/0.58           = (k5_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 0.21/0.58              (k5_xboole_0 @ X16 @ X17)))),
% 0.21/0.58      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((k2_xboole_0 @ X0 @ X1)
% 0.21/0.58           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['40', '43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.21/0.58         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.21/0.58         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 0.21/0.58            (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.21/0.58      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.58  thf('48', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['39', '47'])).
% 0.21/0.58  thf('49', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('50', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
