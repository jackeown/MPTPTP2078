%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvEXPBYeeK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:09 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 122 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  436 ( 744 expanded)
%              Number of equality atoms :   55 ( 101 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k5_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_xboole_0 @ X29 @ X31 )
      | ( ( k4_xboole_0 @ X29 @ X31 )
       != X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','41'])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('46',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvEXPBYeeK
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.50/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.69  % Solved by: fo/fo7.sh
% 0.50/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.69  % done 753 iterations in 0.243s
% 0.50/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.69  % SZS output start Refutation
% 0.50/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.69  thf(t46_zfmisc_1, conjecture,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.50/0.69       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.50/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.69    (~( ![A:$i,B:$i]:
% 0.50/0.69        ( ( r2_hidden @ A @ B ) =>
% 0.50/0.69          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.50/0.69    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.50/0.69  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf(l1_zfmisc_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.50/0.69  thf('1', plain,
% 0.50/0.69      (![X44 : $i, X46 : $i]:
% 0.50/0.69         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 0.50/0.69      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.50/0.69  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.50/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.69  thf(t28_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.69  thf('3', plain,
% 0.50/0.69      (![X23 : $i, X24 : $i]:
% 0.50/0.69         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.50/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.69  thf('4', plain,
% 0.50/0.69      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.50/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.69  thf('5', plain,
% 0.50/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.69  thf('6', plain,
% 0.50/0.69      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.50/0.69      inference('demod', [status(thm)], ['4', '5'])).
% 0.50/0.69  thf('7', plain,
% 0.50/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.69  thf(t100_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.50/0.69  thf('8', plain,
% 0.50/0.69      (![X20 : $i, X21 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ X20 @ X21)
% 0.50/0.69           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.69  thf('9', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.50/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['7', '8'])).
% 0.50/0.69  thf('10', plain,
% 0.50/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.50/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['6', '9'])).
% 0.50/0.69  thf(t39_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.50/0.69  thf('11', plain,
% 0.50/0.69      (![X25 : $i, X26 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.50/0.69           = (k2_xboole_0 @ X25 @ X26))),
% 0.50/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.50/0.69  thf('12', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.69  thf(t1_boole, axiom,
% 0.50/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.69  thf('13', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.69  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf('15', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['11', '14'])).
% 0.50/0.69  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.69  thf(t98_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.50/0.69  thf('18', plain,
% 0.50/0.69      (![X32 : $i, X33 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X32 @ X33)
% 0.50/0.69           = (k5_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X32)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.50/0.69  thf('19', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.69  thf(t40_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.50/0.69  thf('20', plain,
% 0.50/0.69      (![X27 : $i, X28 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.50/0.69           = (k4_xboole_0 @ X27 @ X28))),
% 0.50/0.69      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.50/0.69  thf('21', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.50/0.69           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['19', '20'])).
% 0.50/0.69  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.50/0.69  thf(t83_xboole_1, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.50/0.69  thf('23', plain,
% 0.50/0.69      (![X29 : $i, X31 : $i]:
% 0.50/0.69         ((r1_xboole_0 @ X29 @ X31) | ((k4_xboole_0 @ X29 @ X31) != (X29)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.50/0.69  thf('24', plain,
% 0.50/0.69      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.50/0.69  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.50/0.69      inference('simplify', [status(thm)], ['24'])).
% 0.50/0.69  thf(symmetry_r1_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.50/0.69  thf('26', plain,
% 0.50/0.69      (![X11 : $i, X12 : $i]:
% 0.50/0.69         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.50/0.69      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.50/0.69  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.50/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.69  thf('28', plain,
% 0.50/0.69      (![X29 : $i, X30 : $i]:
% 0.50/0.69         (((k4_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_xboole_0 @ X29 @ X30))),
% 0.50/0.69      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.50/0.69  thf('29', plain,
% 0.50/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.50/0.69  thf('30', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.50/0.69      inference('demod', [status(thm)], ['21', '29'])).
% 0.50/0.69  thf('31', plain,
% 0.50/0.69      (![X0 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.50/0.69  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['12', '13'])).
% 0.50/0.69  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.50/0.69  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.69      inference('demod', [status(thm)], ['30', '33'])).
% 0.50/0.69  thf(d10_xboole_0, axiom,
% 0.50/0.69    (![A:$i,B:$i]:
% 0.50/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.69  thf('35', plain,
% 0.50/0.69      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.50/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.50/0.69  thf('36', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.50/0.69      inference('simplify', [status(thm)], ['35'])).
% 0.50/0.69  thf('37', plain,
% 0.50/0.69      (![X23 : $i, X24 : $i]:
% 0.50/0.69         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.50/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.50/0.69  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.50/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.69  thf('39', plain,
% 0.50/0.69      (![X20 : $i, X21 : $i]:
% 0.50/0.69         ((k4_xboole_0 @ X20 @ X21)
% 0.50/0.69           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.50/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.50/0.69  thf('40', plain,
% 0.50/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.50/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.50/0.69  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.69      inference('demod', [status(thm)], ['34', '40'])).
% 0.50/0.69  thf('42', plain,
% 0.50/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.50/0.69      inference('demod', [status(thm)], ['10', '41'])).
% 0.50/0.69  thf('43', plain,
% 0.50/0.69      (![X25 : $i, X26 : $i]:
% 0.50/0.69         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.50/0.69           = (k2_xboole_0 @ X25 @ X26))),
% 0.50/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.50/0.69  thf('44', plain,
% 0.50/0.69      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.50/0.69         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.50/0.69      inference('sup+', [status(thm)], ['42', '43'])).
% 0.50/0.69  thf('45', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.50/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.50/0.69  thf('46', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.50/0.69      inference('demod', [status(thm)], ['44', '45'])).
% 0.50/0.69  thf('47', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.50/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.69  thf('48', plain,
% 0.50/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.50/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.50/0.69  thf('49', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.50/0.69      inference('demod', [status(thm)], ['47', '48'])).
% 0.50/0.69  thf('50', plain, ($false),
% 0.50/0.69      inference('simplify_reflect-', [status(thm)], ['46', '49'])).
% 0.50/0.69  
% 0.50/0.69  % SZS output end Refutation
% 0.50/0.69  
% 0.50/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
