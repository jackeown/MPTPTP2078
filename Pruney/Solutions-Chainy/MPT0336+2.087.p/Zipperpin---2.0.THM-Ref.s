%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4U1jWaOYuN

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 106 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   17
%              Number of atoms          :  500 ( 817 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) )
        = X28 )
      | ( r2_hidden @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['36','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4U1jWaOYuN
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:34 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  % Running portfolio for 600 s
% 0.18/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.18/0.34  % Number of cores: 8
% 0.18/0.34  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 1.15/1.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.33  % Solved by: fo/fo7.sh
% 1.15/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.33  % done 2532 iterations in 0.884s
% 1.15/1.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.33  % SZS output start Refutation
% 1.15/1.33  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.15/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.33  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.33  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.33  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.15/1.33  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.15/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.33  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.33  thf(t149_zfmisc_1, conjecture,
% 1.15/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.33     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.15/1.33         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.15/1.33       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.15/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.33    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.33        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.15/1.33            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.15/1.33          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.15/1.33    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.15/1.33  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(symmetry_r1_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.15/1.33  thf('2', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.15/1.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.33  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.15/1.33      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.33  thf('4', plain,
% 1.15/1.33      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(commutativity_k3_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.15/1.33  thf('5', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.33  thf('6', plain,
% 1.15/1.33      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.15/1.33      inference('demod', [status(thm)], ['4', '5'])).
% 1.15/1.33  thf(t65_zfmisc_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.15/1.33       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.15/1.33  thf('7', plain,
% 1.15/1.33      (![X28 : $i, X29 : $i]:
% 1.15/1.33         (((k4_xboole_0 @ X28 @ (k1_tarski @ X29)) = (X28))
% 1.15/1.33          | (r2_hidden @ X29 @ X28))),
% 1.15/1.33      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.15/1.33  thf(t79_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.15/1.33  thf('8', plain,
% 1.15/1.33      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 1.15/1.33      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.15/1.33  thf('9', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.15/1.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.33  thf('10', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['8', '9'])).
% 1.15/1.33  thf('11', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 1.15/1.33      inference('sup+', [status(thm)], ['7', '10'])).
% 1.15/1.33  thf(t70_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.15/1.33            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.15/1.33       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.15/1.33            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.15/1.33  thf('12', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i, X18 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X15 @ X16)
% 1.15/1.33          | ~ (r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X18)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.15/1.33  thf('13', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.33         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.15/1.33          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.15/1.33      inference('sup-', [status(thm)], ['11', '12'])).
% 1.15/1.33  thf('14', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf('16', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.15/1.33          | ~ (r1_xboole_0 @ X15 @ X16)
% 1.15/1.33          | ~ (r1_xboole_0 @ X15 @ X17))),
% 1.15/1.33      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.15/1.33  thf('17', plain,
% 1.15/1.33      (![X0 : $i]:
% 1.15/1.33         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 1.15/1.33          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['15', '16'])).
% 1.15/1.33  thf('18', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.15/1.33      inference('sup-', [status(thm)], ['14', '17'])).
% 1.15/1.33  thf('19', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.15/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.33  thf(t3_xboole_0, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.15/1.33            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.15/1.33       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.15/1.33            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.15/1.33  thf('20', plain,
% 1.15/1.33      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.15/1.33         (~ (r2_hidden @ X6 @ X4)
% 1.15/1.33          | ~ (r2_hidden @ X6 @ X7)
% 1.15/1.33          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.15/1.33      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.15/1.33  thf('21', plain,
% 1.15/1.33      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['19', '20'])).
% 1.15/1.33  thf('22', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.15/1.33      inference('sup-', [status(thm)], ['18', '21'])).
% 1.15/1.33  thf('23', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.15/1.33      inference('sup-', [status(thm)], ['13', '22'])).
% 1.15/1.33  thf(t83_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.33  thf('24', plain,
% 1.15/1.33      (![X21 : $i, X22 : $i]:
% 1.15/1.33         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 1.15/1.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.33  thf('25', plain,
% 1.15/1.33      (((k4_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 1.15/1.33      inference('sup-', [status(thm)], ['23', '24'])).
% 1.15/1.33  thf(t106_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i,C:$i]:
% 1.15/1.33     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.15/1.33       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.15/1.33  thf('26', plain,
% 1.15/1.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X8 @ X10)
% 1.15/1.33          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.15/1.33  thf('27', plain,
% 1.15/1.33      (![X0 : $i]:
% 1.15/1.33         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 1.15/1.33      inference('sup-', [status(thm)], ['25', '26'])).
% 1.15/1.33  thf('28', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.15/1.33      inference('sup-', [status(thm)], ['6', '27'])).
% 1.15/1.33  thf('29', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.15/1.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.33  thf('30', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 1.15/1.33      inference('sup-', [status(thm)], ['28', '29'])).
% 1.15/1.33  thf('31', plain,
% 1.15/1.33      (![X21 : $i, X22 : $i]:
% 1.15/1.33         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 1.15/1.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.33  thf('32', plain,
% 1.15/1.33      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.15/1.33      inference('sup-', [status(thm)], ['30', '31'])).
% 1.15/1.33  thf(t48_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]:
% 1.15/1.33     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.15/1.33  thf('33', plain,
% 1.15/1.33      (![X13 : $i, X14 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.33           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.33  thf('34', plain,
% 1.15/1.33      (![X13 : $i, X14 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.33           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.33  thf('35', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.15/1.33           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.33      inference('sup+', [status(thm)], ['33', '34'])).
% 1.15/1.33  thf('36', plain,
% 1.15/1.33      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 1.15/1.33      inference('demod', [status(thm)], ['32', '35'])).
% 1.15/1.33  thf('37', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['8', '9'])).
% 1.15/1.33  thf('38', plain,
% 1.15/1.33      (![X21 : $i, X22 : $i]:
% 1.15/1.33         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 1.15/1.33      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.15/1.33  thf('39', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['37', '38'])).
% 1.15/1.33  thf(t36_xboole_1, axiom,
% 1.15/1.33    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.15/1.33  thf('40', plain,
% 1.15/1.33      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 1.15/1.33      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.33  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.15/1.33      inference('sup+', [status(thm)], ['39', '40'])).
% 1.15/1.33  thf('42', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.33      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.33  thf('43', plain,
% 1.15/1.33      (![X13 : $i, X14 : $i]:
% 1.15/1.33         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.15/1.33           = (k3_xboole_0 @ X13 @ X14))),
% 1.15/1.33      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.15/1.33  thf('44', plain,
% 1.15/1.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.33         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.15/1.33  thf('45', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.33         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 1.15/1.33      inference('sup-', [status(thm)], ['43', '44'])).
% 1.15/1.33  thf('46', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.33         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 1.15/1.33      inference('sup-', [status(thm)], ['42', '45'])).
% 1.15/1.33  thf('47', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.15/1.33      inference('sup-', [status(thm)], ['41', '46'])).
% 1.15/1.33  thf('48', plain,
% 1.15/1.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X8 @ X10)
% 1.15/1.33          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 1.15/1.33      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.15/1.33  thf('49', plain,
% 1.15/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.33         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0)),
% 1.15/1.33      inference('sup-', [status(thm)], ['47', '48'])).
% 1.15/1.33  thf('50', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.15/1.33      inference('sup+', [status(thm)], ['36', '49'])).
% 1.15/1.33  thf('51', plain,
% 1.15/1.33      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.15/1.33          | ~ (r1_xboole_0 @ X15 @ X16)
% 1.15/1.33          | ~ (r1_xboole_0 @ X15 @ X17))),
% 1.15/1.33      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.15/1.33  thf('52', plain,
% 1.15/1.33      (![X0 : $i]:
% 1.15/1.33         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.15/1.33          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.15/1.33      inference('sup-', [status(thm)], ['50', '51'])).
% 1.15/1.33  thf('53', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.15/1.33      inference('sup-', [status(thm)], ['3', '52'])).
% 1.15/1.33  thf('54', plain,
% 1.15/1.33      (![X2 : $i, X3 : $i]:
% 1.15/1.33         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.15/1.33      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.15/1.33  thf('55', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.15/1.33      inference('sup-', [status(thm)], ['53', '54'])).
% 1.15/1.33  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.15/1.33  
% 1.15/1.33  % SZS output end Refutation
% 1.15/1.33  
% 1.15/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
