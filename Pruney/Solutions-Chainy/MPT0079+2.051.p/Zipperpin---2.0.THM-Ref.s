%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArCOCvwETW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:04 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   67 (  79 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  427 ( 580 expanded)
%              Number of equality atoms :   52 (  72 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('13',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_D ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ X0 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ sk_D ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k2_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['21','26','27','38'])).

thf('40',plain,(
    sk_C != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArCOCvwETW
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:56:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 277 iterations in 0.145s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.38/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.62  thf(t72_xboole_1, conjecture,
% 0.38/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.38/0.62         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.38/0.62       ( ( C ) = ( B ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.62        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.38/0.62            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.38/0.62          ( ( C ) = ( B ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t46_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['0', '1'])).
% 0.38/0.62  thf(t41_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.62       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.38/0.62           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.62  thf(t37_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X12 : $i, X13 : $i]:
% 0.38/0.62         ((r1_tarski @ X12 @ X13)
% 0.38/0.62          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.62         (((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.38/0.62          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.38/0.62        | (r1_tarski @ (k4_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['2', '5'])).
% 0.38/0.62  thf('7', plain, ((r1_xboole_0 @ sk_C @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(d7_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.38/0.62       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.62  thf('9', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf(t47_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22))
% 0.38/0.62           = (k4_xboole_0 @ X21 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.38/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.62  thf(t3_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.62  thf('12', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.62  thf('13', plain, (((sk_C) = (k4_xboole_0 @ sk_C @ sk_A))),
% 0.38/0.62      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C @ sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['6', '13'])).
% 0.38/0.62  thf('15', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.38/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.38/0.62  thf(t12_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X5 : $i, X6 : $i]:
% 0.38/0.62         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.38/0.62      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.62  thf('17', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C @ sk_D))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t24_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.38/0.62       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.38/0.62           = (k3_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X10)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t24_xboole_1])).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((k2_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ sk_D))
% 0.38/0.62           = (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ X0) @ 
% 0.38/0.62              (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['18', '19'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (((k2_xboole_0 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_D))
% 0.38/0.62         = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['17', '20'])).
% 0.38/0.62  thf('22', plain, ((r1_xboole_0 @ sk_D @ sk_B)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i]:
% 0.38/0.62         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.38/0.62  thf('24', plain, ((r1_xboole_0 @ sk_B @ sk_D)),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.38/0.62      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.38/0.62  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.62  thf(t1_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.62  thf('27', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.62  thf('28', plain, (![X7 : $i]: ((k2_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.38/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.62  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.62  thf(t53_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.38/0.62       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 0.38/0.62           = (k3_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ 
% 0.38/0.62              (k4_xboole_0 @ X25 @ X27)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t53_xboole_1])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.38/0.62           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf(t2_boole, axiom,
% 0.38/0.62    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_boole])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.62  thf(t48_xboole_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      (![X23 : $i, X24 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 0.38/0.62           = (k3_xboole_0 @ X23 @ X24))),
% 0.38/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.38/0.62           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.38/0.62  thf('39', plain, (((sk_C) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['21', '26', '27', '38'])).
% 0.38/0.62  thf('40', plain, (((sk_C) != (sk_B))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('41', plain, ($false),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
