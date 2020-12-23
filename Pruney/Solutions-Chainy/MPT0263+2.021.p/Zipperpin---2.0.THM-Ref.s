%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kl2izXl1u

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:33 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   71 (  94 expanded)
%              Number of leaves         :   18 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  506 ( 747 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X28 ) @ X29 )
      | ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ~ ( r2_hidden @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ~ ( r2_hidden @ sk_A @ X1 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X1 @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0kl2izXl1u
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:49:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 1703 iterations in 0.751s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.20  thf(t48_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.00/1.20           = (k3_xboole_0 @ X20 @ X21))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.00/1.20           = (k3_xboole_0 @ X20 @ X21))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.20           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['0', '1'])).
% 1.00/1.20  thf(t47_xboole_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.00/1.20  thf('3', plain,
% 1.00/1.20      (![X18 : $i, X19 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19))
% 1.00/1.20           = (k4_xboole_0 @ X18 @ X19))),
% 1.00/1.20      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.00/1.20           = (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.20      inference('sup+', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf(l27_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      (![X28 : $i, X29 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ (k1_tarski @ X28) @ X29) | (r2_hidden @ X28 @ X29))),
% 1.00/1.20      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.00/1.20  thf(d7_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.00/1.20       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.20  thf('7', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ X1 @ X0)
% 1.00/1.20          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 1.00/1.20          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 1.00/1.20      inference('sup+', [status(thm)], ['4', '7'])).
% 1.00/1.20  thf('9', plain,
% 1.00/1.20      (![X28 : $i, X29 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ (k1_tarski @ X28) @ X29) | (r2_hidden @ X28 @ X29))),
% 1.00/1.20      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.00/1.20  thf(t58_zfmisc_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.00/1.20       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i]:
% 1.00/1.20        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 1.00/1.20          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 1.00/1.20  thf('10', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.00/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.00/1.20  thf(t3_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.00/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (![X13 : $i, X14 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      (![X13 : $i, X14 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf(d5_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i,C:$i]:
% 1.00/1.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.00/1.20       ( ![D:$i]:
% 1.00/1.20         ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X6 @ X5)
% 1.00/1.20          | ~ (r2_hidden @ X6 @ X4)
% 1.00/1.20          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X6 @ X4)
% 1.00/1.20          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['14'])).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.00/1.20          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['13', '15'])).
% 1.00/1.20  thf('17', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 1.00/1.20          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['12', '16'])).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 1.00/1.20      inference('simplify', [status(thm)], ['17'])).
% 1.00/1.20  thf('19', plain,
% 1.00/1.20      (![X8 : $i, X9 : $i]:
% 1.00/1.20         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 1.00/1.20      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.00/1.20  thf('20', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 1.00/1.20  thf(commutativity_k3_xboole_0, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.20  thf('22', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.00/1.20      inference('demod', [status(thm)], ['20', '21'])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.00/1.20           = (k3_xboole_0 @ X20 @ X21))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('24', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.00/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X2 @ X3)
% 1.00/1.20          | (r2_hidden @ X2 @ X4)
% 1.00/1.20          | (r2_hidden @ X2 @ X5)
% 1.00/1.20          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.00/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.00/1.20         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 1.00/1.20          | (r2_hidden @ X2 @ X4)
% 1.00/1.20          | ~ (r2_hidden @ X2 @ X3))),
% 1.00/1.20      inference('simplify', [status(thm)], ['25'])).
% 1.00/1.20  thf('27', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r2_hidden @ sk_A @ X0)
% 1.00/1.20          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['24', '26'])).
% 1.00/1.20  thf('28', plain,
% 1.00/1.20      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X15 @ X13)
% 1.00/1.20          | ~ (r2_hidden @ X15 @ X16)
% 1.00/1.20          | ~ (r1_xboole_0 @ X13 @ X16))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ sk_A @ X0)
% 1.00/1.20          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 1.00/1.20          | ~ (r2_hidden @ sk_A @ X1))),
% 1.00/1.20      inference('sup-', [status(thm)], ['27', '28'])).
% 1.00/1.20  thf('30', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 1.00/1.20          | ~ (r2_hidden @ sk_A @ X1)
% 1.00/1.20          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['23', '29'])).
% 1.00/1.20  thf('31', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 1.00/1.20          | (r2_hidden @ sk_A @ 
% 1.00/1.20             (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X1 @ sk_B)))
% 1.00/1.20          | ~ (r2_hidden @ sk_A @ X0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['22', '30'])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      (![X13 : $i, X14 : $i]:
% 1.00/1.20         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.00/1.20  thf(t3_boole, axiom,
% 1.00/1.20    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.00/1.20  thf('33', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X6 @ X4)
% 1.00/1.20          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['14'])).
% 1.00/1.20  thf('35', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 1.00/1.20  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.00/1.20      inference('condensation', [status(thm)], ['35'])).
% 1.00/1.20  thf('37', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.00/1.20      inference('sup-', [status(thm)], ['32', '36'])).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]:
% 1.00/1.20         ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X1 @ sk_B)))
% 1.00/1.20          | ~ (r2_hidden @ sk_A @ X0))),
% 1.00/1.20      inference('demod', [status(thm)], ['31', '37'])).
% 1.00/1.20  thf('39', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['11', '38'])).
% 1.00/1.20  thf('40', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.00/1.20         (~ (r2_hidden @ X6 @ X4)
% 1.00/1.20          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.00/1.20      inference('simplify', [status(thm)], ['14'])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      (![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 1.00/1.20      inference('sup-', [status(thm)], ['39', '40'])).
% 1.00/1.20  thf('42', plain,
% 1.00/1.20      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['8', '41'])).
% 1.00/1.20  thf('43', plain,
% 1.00/1.20      (![X20 : $i, X21 : $i]:
% 1.00/1.20         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 1.00/1.20           = (k3_xboole_0 @ X20 @ X21))),
% 1.00/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.20  thf('44', plain,
% 1.00/1.20      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 1.00/1.20         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 1.00/1.20      inference('sup+', [status(thm)], ['42', '43'])).
% 1.00/1.20  thf('45', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.00/1.20      inference('cnf', [status(esa)], [t3_boole])).
% 1.00/1.20  thf('46', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.20  thf('47', plain,
% 1.00/1.20      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.00/1.20  thf('48', plain,
% 1.00/1.20      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('49', plain,
% 1.00/1.20      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.00/1.20      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 1.00/1.20      inference('demod', [status(thm)], ['48', '49'])).
% 1.00/1.20  thf('51', plain, ($false),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['47', '50'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
