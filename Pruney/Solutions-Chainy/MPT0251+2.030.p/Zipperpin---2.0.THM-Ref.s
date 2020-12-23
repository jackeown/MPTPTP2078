%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iUK3muKfps

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:05 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 124 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  392 ( 790 expanded)
%              Number of equality atoms :   49 ( 102 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X40: $i,X42: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X40 ) @ X42 )
      | ~ ( r2_hidden @ X40 @ X42 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','12','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('44',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iUK3muKfps
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 711 iterations in 0.235s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.69  thf(t46_zfmisc_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.46/0.69       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( r2_hidden @ A @ B ) =>
% 0.46/0.69          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.46/0.69  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(l1_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      (![X40 : $i, X42 : $i]:
% 0.46/0.69         ((r1_tarski @ (k1_tarski @ X40) @ X42) | ~ (r2_hidden @ X40 @ X42))),
% 0.46/0.69      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.46/0.69  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf(t28_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X20 : $i, X21 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.69  thf(t100_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (![X17 : $i, X18 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X17 @ X18)
% 0.46/0.69           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.69  thf(d10_xboole_0, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.46/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.69  thf('8', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.46/0.69      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X20 : $i, X21 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (![X17 : $i, X18 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X17 @ X18)
% 0.46/0.69           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf(commutativity_k2_tarski, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i]:
% 0.46/0.69         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.69  thf(l51_zfmisc_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X43 : $i, X44 : $i]:
% 0.46/0.69         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.46/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X43 : $i, X44 : $i]:
% 0.46/0.69         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.46/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf(t1_boole, axiom,
% 0.46/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.69  thf('18', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.46/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.69  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf(t40_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X24 : $i, X25 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25)
% 0.46/0.69           = (k4_xboole_0 @ X24 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.46/0.69         = (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '12', '21'])).
% 0.46/0.69  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf(t7_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.69  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.69      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (![X20 : $i, X21 : $i]:
% 0.46/0.69         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X17 : $i, X18 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ X17 @ X18)
% 0.46/0.69           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.69           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf(t39_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.46/0.69           = (k2_xboole_0 @ X22 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.69  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.69  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.69      inference('sup+', [status(thm)], ['33', '34'])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['29', '30', '35'])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['22', '36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i]:
% 0.46/0.69         ((k2_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22))
% 0.46/0.69           = (k2_xboole_0 @ X22 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.46/0.69         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.69      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.69  thf('40', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.46/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.69  thf('41', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.46/0.69  thf('42', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.46/0.69      inference('sup+', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf('44', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.69  thf('45', plain, ($false),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
