%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CTTyFoBlHk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:29 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 199 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  527 (1472 expanded)
%              Number of equality atoms :   35 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('11',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_A ) @ sk_A )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) )
    = sk_A ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X33 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('24',plain,(
    r1_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k5_xboole_0 @ sk_A @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','26'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30','33','34'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X15 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X33 @ X34 ) @ X34 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('45',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['29','30','33','34'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('52',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ( r1_xboole_0 @ X29 @ X30 )
      | ~ ( r1_xboole_0 @ X29 @ ( k2_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('56',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['43','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CTTyFoBlHk
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 175 iterations in 0.043s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(t106_xboole_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.19/0.49          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf(t36_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.19/0.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.49  thf('3', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf(t100_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X13 @ X14)
% 0.19/0.49           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf(t7_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X12 : $i]:
% 0.19/0.49         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i]: (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X21)),
% 0.19/0.49      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.19/0.49  thf('11', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A)),
% 0.19/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (((k3_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_A) @ sk_A)
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.49  thf(t4_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.19/0.49          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.19/0.49          | ~ (r1_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.19/0.49         = (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.49  thf(t48_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 0.19/0.49           = (k3_xboole_0 @ X26 @ X27))),
% 0.19/0.49      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A))
% 0.19/0.49         = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A)) = (sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf(t79_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X33 : $i, X34 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X33 @ X34) @ X34)),
% 0.19/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.49  thf('24', plain, ((r1_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['17', '24'])).
% 0.19/0.49  thf('26', plain, (((k5_xboole_0 @ sk_A @ sk_A) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '25'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['7', '26'])).
% 0.19/0.49  thf(t39_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i]:
% 0.19/0.49         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.19/0.49           = (k2_xboole_0 @ X23 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ k1_xboole_0)
% 0.19/0.49         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.19/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf(commutativity_k2_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.49  thf(t1_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('32', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_boole])).
% 0.19/0.49  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.19/0.49         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['29', '30', '33', '34'])).
% 0.19/0.49  thf(t11_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.19/0.49         ((r1_tarski @ X15 @ X16)
% 0.19/0.49          | ~ (r1_tarski @ (k2_xboole_0 @ X15 @ X17) @ X16))),
% 0.19/0.49      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)
% 0.19/0.49          | (r1_tarski @ sk_A @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.49  thf('38', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('40', plain, (((r1_tarski @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (~ ((r1_xboole_0 @ sk_A @ sk_C_1)) | ~ ((r1_tarski @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('42', plain, (~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.19/0.49  thf('43', plain, (~ (r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (![X33 : $i, X34 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X33 @ X34) @ X34)),
% 0.19/0.49      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X8 @ X9)
% 0.19/0.49          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.19/0.49          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.49          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '49'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((k4_xboole_0 @ sk_B_1 @ sk_C_1)
% 0.19/0.49         = (k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['29', '30', '33', '34'])).
% 0.19/0.49  thf(t70_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.19/0.49            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.19/0.49       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.19/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X29 : $i, X30 : $i, X32 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X29 @ X30)
% 0.19/0.49          | ~ (r1_xboole_0 @ X29 @ (k2_xboole_0 @ X30 @ X32)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.19/0.49          | (r1_xboole_0 @ X0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf('54', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.19/0.49      inference('sup-', [status(thm)], ['50', '53'])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.19/0.49  thf('56', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.49  thf('57', plain, ($false), inference('demod', [status(thm)], ['43', '56'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
