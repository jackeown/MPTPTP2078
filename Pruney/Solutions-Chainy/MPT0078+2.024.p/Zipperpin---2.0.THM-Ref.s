%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsAeEDqRo3

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:55 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   75 (  99 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  485 ( 769 expanded)
%              Number of equality atoms :   31 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['2','9'])).

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

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ X0 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X29 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('27',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    r1_tarski @ sk_C_2 @ ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('32',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('37',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X29 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ ( k4_xboole_0 @ sk_C_2 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( ( k4_xboole_0 @ X13 @ X12 )
       != ( k4_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
     != k1_xboole_0 )
    | ( sk_A = sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C_2 )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JsAeEDqRo3
% 0.14/0.37  % Computer   : n013.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:14:25 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.23/0.37  % Running portfolio for 600 s
% 0.23/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 497 iterations in 0.154s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(t71_xboole_1, conjecture,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.46/0.63         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.46/0.63       ( ( A ) = ( C ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.63        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.46/0.63            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.46/0.63          ( ( A ) = ( C ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.46/0.63  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(symmetry_r1_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.63  thf('2', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf(t7_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_2 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(t43_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.46/0.63       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.63          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_A @ sk_B))
% 0.46/0.63          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.63  thf(t63_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.46/0.63       ( r1_xboole_0 @ A @ C ) ))).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X21 @ X22)
% 0.46/0.63          | ~ (r1_xboole_0 @ X22 @ X23)
% 0.46/0.63          | (r1_xboole_0 @ X21 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ X0)
% 0.46/0.63          | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_A)),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '9'])).
% 0.46/0.63  thf(t3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.63            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.63  thf(t4_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.63            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.63       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.63            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.46/0.63          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.63          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.63          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_C_2)) @ 
% 0.46/0.63          X0)),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '15'])).
% 0.46/0.63  thf(t48_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.63           = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.46/0.63           = (k3_xboole_0 @ X19 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.63           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['17', '18'])).
% 0.46/0.63  thf(t47_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         ((k4_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18))
% 0.46/0.63           = (k4_xboole_0 @ X17 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_2) @ X0)),
% 0.46/0.63      inference('demod', [status(thm)], ['16', '21'])).
% 0.46/0.63  thf(t66_xboole_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.46/0.63       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X29 : $i]: (((X29) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X29 @ X29))),
% 0.46/0.63      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.46/0.63  thf('24', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf('25', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.63  thf('27', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_2 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.46/0.63  thf('30', plain, ((r1_tarski @ sk_C_2 @ (k2_xboole_0 @ sk_A @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['28', '29'])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.63         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 0.46/0.63          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.46/0.63  thf('32', plain, ((r1_tarski @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X21 @ X22)
% 0.46/0.63          | ~ (r1_xboole_0 @ X22 @ X23)
% 0.46/0.63          | (r1_xboole_0 @ X21 @ X23))),
% 0.46/0.63      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ X0)
% 0.46/0.63          | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.63  thf('35', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_C_2 @ sk_A) @ sk_C_2)),
% 0.46/0.63      inference('sup-', [status(thm)], ['27', '34'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.46/0.63      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.46/0.63  thf('37', plain, ((r1_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X4 : $i, X5 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.46/0.63         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.46/0.63          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.63          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (r1_xboole_0 @ 
% 0.46/0.63          (k3_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A)) @ X0)),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (![X29 : $i]: (((X29) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X29 @ X29))),
% 0.46/0.63      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.46/0.63  thf('43', plain,
% 0.46/0.63      (((k3_xboole_0 @ sk_C_2 @ (k4_xboole_0 @ sk_C_2 @ sk_A)) = (k1_xboole_0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.46/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.63      inference('sup+', [status(thm)], ['19', '20'])).
% 0.46/0.63  thf('45', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 0.46/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.63  thf(t32_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.46/0.63       ( ( A ) = ( B ) ) ))).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i]:
% 0.46/0.63         (((X13) = (X12))
% 0.46/0.63          | ((k4_xboole_0 @ X13 @ X12) != (k4_xboole_0 @ X12 @ X13)))),
% 0.46/0.63      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      ((((k4_xboole_0 @ sk_A @ sk_C_2) != (k1_xboole_0)) | ((sk_A) = (sk_C_2)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.63  thf('48', plain, (((sk_A) != (sk_C_2))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('49', plain, (((k4_xboole_0 @ sk_A @ sk_C_2) != (k1_xboole_0))),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('50', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['24', '49'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
