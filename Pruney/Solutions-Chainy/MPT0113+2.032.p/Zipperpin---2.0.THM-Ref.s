%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBP55lmRVJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 115 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  523 ( 794 expanded)
%              Number of equality atoms :   41 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
   <= ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

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

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X12: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X14 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( ( k4_xboole_0 @ X12 @ X13 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['19','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBP55lmRVJ
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:03:53 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.34  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 247 iterations in 0.090s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(t106_xboole_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.53          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_A @ sk_B) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_A @ sk_B)) <= (~ ((r1_tarski @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.53  thf('4', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t28_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(t49_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.20/0.53       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.20/0.53           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.53  thf(d5_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.53          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.53          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.53          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ X3 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ sk_A @ X0)
% 0.20/0.53          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_A @ sk_C_1) | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '12'])).
% 0.20/0.53  thf('14', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.20/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('16', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('18', plain, (~ ((r1_tarski @ sk_A @ sk_B))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.20/0.53  thf(t36_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf(l32_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X12 : $i, X14 : $i]:
% 0.20/0.53         (((k4_xboole_0 @ X12 @ X14) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.20/0.53           = (k4_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ sk_A @ 
% 0.20/0.53           (k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ X0))
% 0.20/0.53           = (k4_xboole_0 @ sk_A @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.20/0.53      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.20/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.20/0.53           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.54           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf(t17_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 0.20/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.54      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['31', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.54           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf(t100_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X15 : $i, X16 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ X15 @ X16)
% 0.20/0.54           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.54  thf('39', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.54           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf(t92_xboole_1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.54  thf('40', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.54           = (k1_xboole_0))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.20/0.54           = (k4_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((r1_tarski @ X12 @ X13)
% 0.20/0.54          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.54  thf('55', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.54      inference('demod', [status(thm)], ['26', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((r1_tarski @ X12 @ X13)
% 0.20/0.54          | ((k4_xboole_0 @ X12 @ X13) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.20/0.54  thf('59', plain, ($false), inference('demod', [status(thm)], ['19', '58'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
