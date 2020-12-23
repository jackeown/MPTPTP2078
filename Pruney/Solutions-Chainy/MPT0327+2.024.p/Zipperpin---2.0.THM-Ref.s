%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YJXugVAW00

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:53 EST 2020

% Result     : Theorem 2.26s
% Output     : Refutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 112 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  501 ( 786 expanded)
%              Number of equality atoms :   49 (  88 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X34 )
      | ~ ( r2_hidden @ X32 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ~ ( r2_hidden @ X34 @ ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

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
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('25',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('26',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('27',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X24 @ X25 ) @ X25 )
        = X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('43',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('46',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YJXugVAW00
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.26/2.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.26/2.44  % Solved by: fo/fo7.sh
% 2.26/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.26/2.44  % done 2360 iterations in 1.953s
% 2.26/2.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.26/2.44  % SZS output start Refutation
% 2.26/2.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.26/2.44  thf(sk_B_type, type, sk_B: $i).
% 2.26/2.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.26/2.44  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.26/2.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.26/2.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.26/2.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.26/2.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.26/2.44  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.26/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.26/2.44  thf(d5_xboole_0, axiom,
% 2.26/2.44    (![A:$i,B:$i,C:$i]:
% 2.26/2.44     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.26/2.44       ( ![D:$i]:
% 2.26/2.44         ( ( r2_hidden @ D @ C ) <=>
% 2.26/2.44           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.26/2.44  thf('0', plain,
% 2.26/2.44      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.26/2.44         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 2.26/2.44          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 2.26/2.44          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.26/2.44      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.26/2.44  thf(idempotence_k2_xboole_0, axiom,
% 2.26/2.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.26/2.44  thf('1', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 2.26/2.44      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.26/2.44  thf(t46_xboole_1, axiom,
% 2.26/2.44    (![A:$i,B:$i]:
% 2.26/2.44     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 2.26/2.44  thf('2', plain,
% 2.26/2.44      (![X19 : $i, X20 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 2.26/2.44      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.26/2.44  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['1', '2'])).
% 2.26/2.44  thf(t64_zfmisc_1, axiom,
% 2.26/2.44    (![A:$i,B:$i,C:$i]:
% 2.26/2.44     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.26/2.44       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.26/2.44  thf('4', plain,
% 2.26/2.44      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.26/2.44         (((X32) != (X34))
% 2.26/2.44          | ~ (r2_hidden @ X32 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34))))),
% 2.26/2.44      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 2.26/2.44  thf('5', plain,
% 2.26/2.44      (![X33 : $i, X34 : $i]:
% 2.26/2.44         ~ (r2_hidden @ X34 @ (k4_xboole_0 @ X33 @ (k1_tarski @ X34)))),
% 2.26/2.44      inference('simplify', [status(thm)], ['4'])).
% 2.26/2.44  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.26/2.44      inference('sup-', [status(thm)], ['3', '5'])).
% 2.26/2.44  thf('7', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.26/2.44          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.26/2.44      inference('sup-', [status(thm)], ['0', '6'])).
% 2.26/2.44  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['1', '2'])).
% 2.26/2.44  thf(t39_xboole_1, axiom,
% 2.26/2.44    (![A:$i,B:$i]:
% 2.26/2.44     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.26/2.44  thf('9', plain,
% 2.26/2.44      (![X14 : $i, X15 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.26/2.44           = (k2_xboole_0 @ X14 @ X15))),
% 2.26/2.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.26/2.44  thf('10', plain,
% 2.26/2.44      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['8', '9'])).
% 2.26/2.44  thf('11', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 2.26/2.44      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.26/2.44  thf('12', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.26/2.44      inference('demod', [status(thm)], ['10', '11'])).
% 2.26/2.44  thf(commutativity_k2_xboole_0, axiom,
% 2.26/2.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.26/2.44  thf('13', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.26/2.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.26/2.44  thf('14', plain,
% 2.26/2.44      (![X19 : $i, X20 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 2.26/2.44      inference('cnf', [status(esa)], [t46_xboole_1])).
% 2.26/2.44  thf('15', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['13', '14'])).
% 2.26/2.44  thf('16', plain,
% 2.26/2.44      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['12', '15'])).
% 2.26/2.44  thf('17', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 2.26/2.44          | ((X1) = (k1_xboole_0)))),
% 2.26/2.44      inference('demod', [status(thm)], ['7', '16'])).
% 2.26/2.44  thf('18', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.26/2.44      inference('sup+', [status(thm)], ['13', '14'])).
% 2.26/2.44  thf(t41_xboole_1, axiom,
% 2.26/2.44    (![A:$i,B:$i,C:$i]:
% 2.26/2.44     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.26/2.44       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.26/2.44  thf('19', plain,
% 2.26/2.44      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 2.26/2.44           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 2.26/2.44      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.26/2.44  thf('20', plain,
% 2.26/2.44      (![X14 : $i, X15 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.26/2.44           = (k2_xboole_0 @ X14 @ X15))),
% 2.26/2.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.26/2.44  thf('21', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 2.26/2.44           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 2.26/2.44      inference('sup+', [status(thm)], ['19', '20'])).
% 2.26/2.44  thf('22', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 2.26/2.44           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.26/2.44      inference('sup+', [status(thm)], ['18', '21'])).
% 2.26/2.44  thf('23', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.26/2.44      inference('demod', [status(thm)], ['10', '11'])).
% 2.26/2.44  thf('24', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]:
% 2.26/2.44         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.26/2.44      inference('demod', [status(thm)], ['22', '23'])).
% 2.26/2.44  thf(t140_zfmisc_1, conjecture,
% 2.26/2.44    (![A:$i,B:$i]:
% 2.26/2.44     ( ( r2_hidden @ A @ B ) =>
% 2.26/2.44       ( ( k2_xboole_0 @
% 2.26/2.44           ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.26/2.44         ( B ) ) ))).
% 2.26/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.26/2.44    (~( ![A:$i,B:$i]:
% 2.26/2.44        ( ( r2_hidden @ A @ B ) =>
% 2.26/2.44          ( ( k2_xboole_0 @
% 2.26/2.44              ( k4_xboole_0 @ B @ ( k1_tarski @ A ) ) @ ( k1_tarski @ A ) ) =
% 2.26/2.44            ( B ) ) ) )),
% 2.26/2.44    inference('cnf.neg', [status(esa)], [t140_zfmisc_1])).
% 2.26/2.44  thf('25', plain, ((r2_hidden @ sk_A @ sk_B)),
% 2.26/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.44  thf(l1_zfmisc_1, axiom,
% 2.26/2.44    (![A:$i,B:$i]:
% 2.26/2.44     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 2.26/2.44  thf('26', plain,
% 2.26/2.44      (![X29 : $i, X31 : $i]:
% 2.26/2.44         ((r1_tarski @ (k1_tarski @ X29) @ X31) | ~ (r2_hidden @ X29 @ X31))),
% 2.26/2.44      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 2.26/2.44  thf('27', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 2.26/2.44      inference('sup-', [status(thm)], ['25', '26'])).
% 2.26/2.44  thf(t85_xboole_1, axiom,
% 2.26/2.44    (![A:$i,B:$i,C:$i]:
% 2.26/2.44     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.26/2.44  thf('28', plain,
% 2.26/2.44      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.26/2.44         (~ (r1_tarski @ X21 @ X22)
% 2.26/2.44          | (r1_xboole_0 @ X21 @ (k4_xboole_0 @ X23 @ X22)))),
% 2.26/2.44      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.26/2.44  thf('29', plain,
% 2.26/2.44      (![X0 : $i]:
% 2.26/2.44         (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B))),
% 2.26/2.44      inference('sup-', [status(thm)], ['27', '28'])).
% 2.26/2.44  thf(t88_xboole_1, axiom,
% 2.26/2.44    (![A:$i,B:$i]:
% 2.26/2.44     ( ( r1_xboole_0 @ A @ B ) =>
% 2.26/2.44       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 2.26/2.44  thf('30', plain,
% 2.26/2.44      (![X24 : $i, X25 : $i]:
% 2.26/2.44         (((k4_xboole_0 @ (k2_xboole_0 @ X24 @ X25) @ X25) = (X24))
% 2.26/2.44          | ~ (r1_xboole_0 @ X24 @ X25))),
% 2.26/2.44      inference('cnf', [status(esa)], [t88_xboole_1])).
% 2.26/2.44  thf('31', plain,
% 2.26/2.44      (![X0 : $i]:
% 2.26/2.44         ((k4_xboole_0 @ 
% 2.26/2.44           (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B)) @ 
% 2.26/2.44           (k4_xboole_0 @ X0 @ sk_B)) = (k1_tarski @ sk_A))),
% 2.26/2.44      inference('sup-', [status(thm)], ['29', '30'])).
% 2.26/2.44  thf('32', plain,
% 2.26/2.44      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.26/2.44         (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)) = (k1_tarski @ sk_A))),
% 2.26/2.44      inference('sup+', [status(thm)], ['24', '31'])).
% 2.26/2.44  thf('33', plain,
% 2.26/2.44      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.26/2.44         (~ (r2_hidden @ X6 @ X5)
% 2.26/2.44          | ~ (r2_hidden @ X6 @ X4)
% 2.26/2.44          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.26/2.44      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.26/2.44  thf('34', plain,
% 2.26/2.44      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.26/2.44         (~ (r2_hidden @ X6 @ X4)
% 2.26/2.44          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.26/2.44      inference('simplify', [status(thm)], ['33'])).
% 2.26/2.44  thf('35', plain,
% 2.26/2.44      (![X0 : $i]:
% 2.26/2.44         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 2.26/2.44          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 2.26/2.44      inference('sup-', [status(thm)], ['32', '34'])).
% 2.26/2.44  thf('36', plain,
% 2.26/2.44      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.26/2.44         (~ (r2_hidden @ X6 @ X5)
% 2.26/2.44          | (r2_hidden @ X6 @ X3)
% 2.26/2.44          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.26/2.44      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.26/2.44  thf('37', plain,
% 2.26/2.44      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.26/2.44         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.26/2.44      inference('simplify', [status(thm)], ['36'])).
% 2.26/2.44  thf('38', plain,
% 2.26/2.44      (![X0 : $i]:
% 2.26/2.44         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 2.26/2.44      inference('clc', [status(thm)], ['35', '37'])).
% 2.26/2.44  thf('39', plain,
% 2.26/2.44      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 2.26/2.44      inference('sup-', [status(thm)], ['17', '38'])).
% 2.26/2.44  thf('40', plain,
% 2.26/2.44      (![X14 : $i, X15 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.26/2.44           = (k2_xboole_0 @ X14 @ X15))),
% 2.26/2.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.26/2.44  thf('41', plain,
% 2.26/2.44      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 2.26/2.44         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.26/2.44      inference('sup+', [status(thm)], ['39', '40'])).
% 2.26/2.44  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.26/2.44      inference('demod', [status(thm)], ['10', '11'])).
% 2.26/2.44  thf('43', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.26/2.44      inference('demod', [status(thm)], ['41', '42'])).
% 2.26/2.44  thf('44', plain,
% 2.26/2.44      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 2.26/2.44         (k1_tarski @ sk_A)) != (sk_B))),
% 2.26/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.26/2.44  thf('45', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.26/2.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.26/2.44  thf('46', plain,
% 2.26/2.44      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.26/2.44         (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))) != (sk_B))),
% 2.26/2.44      inference('demod', [status(thm)], ['44', '45'])).
% 2.26/2.44  thf('47', plain,
% 2.26/2.44      (![X14 : $i, X15 : $i]:
% 2.26/2.44         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 2.26/2.44           = (k2_xboole_0 @ X14 @ X15))),
% 2.26/2.44      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.26/2.44  thf('48', plain,
% 2.26/2.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.26/2.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.26/2.44  thf('49', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 2.26/2.44      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.26/2.44  thf('50', plain, ($false),
% 2.26/2.44      inference('simplify_reflect-', [status(thm)], ['43', '49'])).
% 2.26/2.44  
% 2.26/2.44  % SZS output end Refutation
% 2.26/2.44  
% 2.26/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
