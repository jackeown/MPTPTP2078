%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpd2XJeMPo

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 111 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  556 ( 860 expanded)
%              Number of equality atoms :   38 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( r1_xboole_0 @ ( k2_tarski @ X29 @ X31 ) @ X30 )
      | ( r2_hidden @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['43','48','49'])).

thf('51',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','50'])).

thf('52',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','56'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jpd2XJeMPo
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/0.97  % Solved by: fo/fo7.sh
% 0.80/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/0.97  % done 1179 iterations in 0.517s
% 0.80/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/0.97  % SZS output start Refutation
% 0.80/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.80/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.80/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.80/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.80/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/0.97  thf(sk_D_type, type, sk_D: $i).
% 0.80/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/0.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/0.97  thf(t149_zfmisc_1, conjecture,
% 0.80/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/0.97     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.80/0.97         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.80/0.97       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.80/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.80/0.97    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.80/0.97        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.80/0.97            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.80/0.97          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.80/0.97    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.80/0.97  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.80/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.97  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.80/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.97  thf(d7_xboole_0, axiom,
% 0.80/0.97    (![A:$i,B:$i]:
% 0.80/0.97     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.80/0.97       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.80/0.97  thf('2', plain,
% 0.80/0.97      (![X2 : $i, X3 : $i]:
% 0.80/0.97         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.80/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/0.97  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.80/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.80/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/0.97  thf('4', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.80/0.97      inference('demod', [status(thm)], ['3', '4'])).
% 0.80/0.97  thf('6', plain,
% 0.80/0.97      (![X2 : $i, X4 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.80/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/0.97  thf('7', plain,
% 0.80/0.97      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.80/0.97      inference('sup-', [status(thm)], ['5', '6'])).
% 0.80/0.97  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.80/0.97      inference('simplify', [status(thm)], ['7'])).
% 0.80/0.97  thf('9', plain,
% 0.80/0.97      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.80/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.97  thf('10', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('11', plain,
% 0.80/0.97      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.80/0.97      inference('demod', [status(thm)], ['9', '10'])).
% 0.80/0.97  thf(t28_xboole_1, axiom,
% 0.80/0.97    (![A:$i,B:$i]:
% 0.80/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.80/0.97  thf('12', plain,
% 0.80/0.97      (![X14 : $i, X15 : $i]:
% 0.80/0.97         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.80/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.80/0.97  thf('13', plain,
% 0.80/0.97      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.80/0.97         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.80/0.97  thf('14', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('15', plain,
% 0.80/0.97      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.80/0.97         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/0.97      inference('demod', [status(thm)], ['13', '14'])).
% 0.80/0.97  thf(t16_xboole_1, axiom,
% 0.80/0.97    (![A:$i,B:$i,C:$i]:
% 0.80/0.97     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.80/0.97       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.80/0.97  thf('16', plain,
% 0.80/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.80/0.97           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.80/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.80/0.97  thf('17', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('18', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.80/0.97           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/0.97      inference('sup+', [status(thm)], ['16', '17'])).
% 0.80/0.97  thf('19', plain,
% 0.80/0.97      (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))
% 0.80/0.97         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/0.97      inference('demod', [status(thm)], ['15', '18'])).
% 0.80/0.97  thf(t69_enumset1, axiom,
% 0.80/0.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.80/0.97  thf('20', plain,
% 0.80/0.97      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.80/0.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/0.97  thf(t57_zfmisc_1, axiom,
% 0.80/0.97    (![A:$i,B:$i,C:$i]:
% 0.80/0.97     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.80/0.97          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.80/0.97  thf('21', plain,
% 0.80/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.80/0.97         ((r2_hidden @ X29 @ X30)
% 0.80/0.97          | (r1_xboole_0 @ (k2_tarski @ X29 @ X31) @ X30)
% 0.80/0.97          | (r2_hidden @ X31 @ X30))),
% 0.80/0.97      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.80/0.97  thf('22', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.80/0.97          | (r2_hidden @ X0 @ X1)
% 0.80/0.97          | (r2_hidden @ X0 @ X1))),
% 0.80/0.97      inference('sup+', [status(thm)], ['20', '21'])).
% 0.80/0.97  thf('23', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]:
% 0.80/0.97         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.80/0.97      inference('simplify', [status(thm)], ['22'])).
% 0.80/0.97  thf(t70_xboole_1, axiom,
% 0.80/0.97    (![A:$i,B:$i,C:$i]:
% 0.80/0.97     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.80/0.97            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.80/0.97       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.80/0.97            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.80/0.97  thf('24', plain,
% 0.80/0.97      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X17 @ X18)
% 0.80/0.97          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 0.80/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.80/0.97  thf('25', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.97         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.80/0.97          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.80/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/0.97  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.80/0.97  thf('26', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.80/0.97      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.80/0.97  thf('27', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.80/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.97  thf('28', plain,
% 0.80/0.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.80/0.97          | ~ (r1_xboole_0 @ X17 @ X18)
% 0.80/0.97          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.80/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.80/0.97  thf('29', plain,
% 0.80/0.97      (![X0 : $i]:
% 0.80/0.97         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.80/0.97          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.80/0.97      inference('sup-', [status(thm)], ['27', '28'])).
% 0.80/0.97  thf('30', plain,
% 0.80/0.97      ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['26', '29'])).
% 0.80/0.97  thf('31', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.80/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.97  thf(t3_xboole_0, axiom,
% 0.80/0.97    (![A:$i,B:$i]:
% 0.80/0.97     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.80/0.97            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/0.97       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/0.97            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.80/0.97  thf('32', plain,
% 0.80/0.97      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.80/0.97         (~ (r2_hidden @ X9 @ X7)
% 0.80/0.97          | ~ (r2_hidden @ X9 @ X10)
% 0.80/0.97          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.80/0.97      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.80/0.97  thf('33', plain,
% 0.80/0.97      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.80/0.97  thf('34', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['30', '33'])).
% 0.80/0.97  thf('35', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.80/0.97      inference('sup-', [status(thm)], ['25', '34'])).
% 0.80/0.97  thf('36', plain,
% 0.80/0.97      (![X2 : $i, X3 : $i]:
% 0.80/0.97         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.80/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/0.97  thf('37', plain,
% 0.80/0.97      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_xboole_0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.80/0.97  thf('38', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('39', plain,
% 0.80/0.97      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.80/0.97      inference('demod', [status(thm)], ['37', '38'])).
% 0.80/0.97  thf('40', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('41', plain,
% 0.80/0.97      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 0.80/0.97           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 0.80/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.80/0.97  thf('42', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.80/0.97           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.80/0.97      inference('sup+', [status(thm)], ['40', '41'])).
% 0.80/0.97  thf('43', plain,
% 0.80/0.97      (![X0 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.80/0.97           = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.80/0.97      inference('sup+', [status(thm)], ['39', '42'])).
% 0.80/0.97  thf('44', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/0.97  thf('45', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.80/0.97      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.80/0.97  thf('46', plain,
% 0.80/0.97      (![X2 : $i, X3 : $i]:
% 0.80/0.97         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.80/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/0.97  thf('47', plain,
% 0.80/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.80/0.97      inference('sup-', [status(thm)], ['45', '46'])).
% 0.80/0.97  thf('48', plain,
% 0.80/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.80/0.97      inference('sup+', [status(thm)], ['44', '47'])).
% 0.80/0.97  thf('49', plain,
% 0.80/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.80/0.97           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/0.97      inference('sup+', [status(thm)], ['16', '17'])).
% 0.80/0.97  thf('50', plain,
% 0.80/0.97      (![X0 : $i]:
% 0.80/0.97         ((k1_xboole_0)
% 0.80/0.97           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D))))),
% 0.80/0.97      inference('demod', [status(thm)], ['43', '48', '49'])).
% 0.80/0.97  thf('51', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.80/0.97      inference('demod', [status(thm)], ['19', '50'])).
% 0.80/0.97  thf('52', plain,
% 0.80/0.97      (![X2 : $i, X4 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.80/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.80/0.97  thf('53', plain,
% 0.80/0.97      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.80/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/0.97  thf('54', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.80/0.97      inference('simplify', [status(thm)], ['53'])).
% 0.80/0.97  thf('55', plain,
% 0.80/0.97      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 0.80/0.97          | ~ (r1_xboole_0 @ X17 @ X18)
% 0.80/0.97          | ~ (r1_xboole_0 @ X17 @ X19))),
% 0.80/0.97      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.80/0.97  thf('56', plain,
% 0.80/0.97      (![X0 : $i]:
% 0.80/0.97         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.80/0.97          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.80/0.97      inference('sup-', [status(thm)], ['54', '55'])).
% 0.80/0.97  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.80/0.97      inference('sup-', [status(thm)], ['8', '56'])).
% 0.80/0.97  thf(symmetry_r1_xboole_0, axiom,
% 0.80/0.97    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.80/0.97  thf('58', plain,
% 0.80/0.97      (![X5 : $i, X6 : $i]:
% 0.80/0.97         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.80/0.97      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.80/0.97  thf('59', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.80/0.97      inference('sup-', [status(thm)], ['57', '58'])).
% 0.80/0.97  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.80/0.97  
% 0.80/0.97  % SZS output end Refutation
% 0.80/0.97  
% 0.80/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
