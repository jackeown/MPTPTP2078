%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RoSA1uU6ht

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:55 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 176 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  635 (1510 expanded)
%              Number of equality atoms :   66 ( 164 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40 != X42 )
      | ~ ( r2_hidden @ X40 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X41: $i,X42: $i] :
      ~ ( r2_hidden @ X42 @ ( k4_xboole_0 @ X41 @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('12',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X36 @ X38 ) @ X39 )
        = ( k1_tarski @ X36 ) )
      | ( X36 != X38 )
      | ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X38 @ X38 ) @ X39 )
        = ( k1_tarski @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k4_xboole_0 @ X32 @ ( k4_xboole_0 @ X33 @ X34 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X32 @ X33 ) @ ( k3_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X8 @ X10 ) @ ( k3_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','48'])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','9','51'])).

thf('53',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('54',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['11','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RoSA1uU6ht
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:20:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.76/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.93  % Solved by: fo/fo7.sh
% 0.76/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.93  % done 820 iterations in 0.490s
% 0.76/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.93  % SZS output start Refutation
% 0.76/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.93  thf(t65_zfmisc_1, conjecture,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/0.93       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.76/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.93    (~( ![A:$i,B:$i]:
% 0.76/0.93        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.76/0.93          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.76/0.93    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.76/0.93  thf('0', plain,
% 0.76/0.93      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.76/0.93        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('1', plain,
% 0.76/0.93      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf('2', plain,
% 0.76/0.93      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.76/0.93       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf('3', plain,
% 0.76/0.93      (((r2_hidden @ sk_B @ sk_A)
% 0.76/0.93        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('4', plain,
% 0.76/0.93      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf('5', plain,
% 0.76/0.93      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.76/0.93         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf(t64_zfmisc_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.76/0.93       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.76/0.93  thf('6', plain,
% 0.76/0.93      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.76/0.93         (((X40) != (X42))
% 0.76/0.93          | ~ (r2_hidden @ X40 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42))))),
% 0.76/0.93      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.76/0.93  thf('7', plain,
% 0.76/0.93      (![X41 : $i, X42 : $i]:
% 0.76/0.93         ~ (r2_hidden @ X42 @ (k4_xboole_0 @ X41 @ (k1_tarski @ X42)))),
% 0.76/0.93      inference('simplify', [status(thm)], ['6'])).
% 0.76/0.93  thf('8', plain,
% 0.76/0.93      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.76/0.93         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/0.93      inference('sup-', [status(thm)], ['5', '7'])).
% 0.76/0.93  thf('9', plain,
% 0.76/0.93      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.76/0.93       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.76/0.93      inference('sup-', [status(thm)], ['4', '8'])).
% 0.76/0.93  thf('10', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.76/0.93      inference('sat_resolution*', [status(thm)], ['2', '9'])).
% 0.76/0.93  thf('11', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.76/0.93      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.76/0.93  thf(l38_zfmisc_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.76/0.93       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.76/0.93         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.76/0.93  thf('12', plain,
% 0.76/0.93      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.76/0.93         (((k4_xboole_0 @ (k2_tarski @ X36 @ X38) @ X39) = (k1_tarski @ X36))
% 0.76/0.93          | ((X36) != (X38))
% 0.76/0.93          | (r2_hidden @ X36 @ X39))),
% 0.76/0.93      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.76/0.93  thf('13', plain,
% 0.76/0.93      (![X38 : $i, X39 : $i]:
% 0.76/0.93         ((r2_hidden @ X38 @ X39)
% 0.76/0.93          | ((k4_xboole_0 @ (k2_tarski @ X38 @ X38) @ X39) = (k1_tarski @ X38)))),
% 0.76/0.93      inference('simplify', [status(thm)], ['12'])).
% 0.76/0.93  thf(t21_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.76/0.93  thf('14', plain,
% 0.76/0.93      (![X14 : $i, X15 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.76/0.93  thf(t47_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('15', plain,
% 0.76/0.93      (![X22 : $i, X23 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.76/0.93           = (k4_xboole_0 @ X22 @ X23))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('16', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.93  thf(t48_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('17', plain,
% 0.76/0.93      (![X24 : $i, X25 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.76/0.93           = (k3_xboole_0 @ X24 @ X25))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('18', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.76/0.93           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['16', '17'])).
% 0.76/0.93  thf('19', plain,
% 0.76/0.93      (![X24 : $i, X25 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.76/0.93           = (k3_xboole_0 @ X24 @ X25))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('20', plain,
% 0.76/0.93      (![X14 : $i, X15 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X14 @ (k2_xboole_0 @ X14 @ X15)) = (X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.76/0.93  thf('21', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.76/0.93  thf(t52_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.76/0.93       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.76/0.93  thf('22', plain,
% 0.76/0.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X32 @ (k4_xboole_0 @ X33 @ X34))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X32 @ X33) @ 
% 0.76/0.93              (k3_xboole_0 @ X32 @ X34)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.76/0.93  thf('23', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/0.93  thf('24', plain,
% 0.76/0.93      (![X24 : $i, X25 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.76/0.93           = (k3_xboole_0 @ X24 @ X25))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf(t41_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.93       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.76/0.93  thf('25', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.76/0.93           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.93  thf('26', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.76/0.93           = (k4_xboole_0 @ X2 @ 
% 0.76/0.93              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))))),
% 0.76/0.93      inference('sup+', [status(thm)], ['24', '25'])).
% 0.76/0.93  thf('27', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X21)
% 0.76/0.93           = (k4_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.76/0.93  thf('28', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 0.76/0.93           = (k4_xboole_0 @ X2 @ 
% 0.76/0.93              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.76/0.93      inference('demod', [status(thm)], ['26', '27'])).
% 0.76/0.93  thf(t111_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.76/0.93       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.76/0.93  thf('29', plain,
% 0.76/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ (k3_xboole_0 @ X8 @ X10) @ (k3_xboole_0 @ X9 @ X10))
% 0.76/0.93           = (k3_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.76/0.93      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.76/0.93  thf(t49_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.76/0.93       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.76/0.93  thf('30', plain,
% 0.76/0.93      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 0.76/0.93           = (k4_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ X28))),
% 0.76/0.93      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.76/0.93  thf(commutativity_k3_xboole_0, axiom,
% 0.76/0.93    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.76/0.93  thf('31', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.76/0.93  thf('32', plain,
% 0.76/0.93      (![X22 : $i, X23 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.76/0.93           = (k4_xboole_0 @ X22 @ X23))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('33', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k4_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['31', '32'])).
% 0.76/0.93  thf('34', plain,
% 0.76/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X8 @ (k4_xboole_0 @ X10 @ X9))
% 0.76/0.93           = (k3_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.76/0.93      inference('demod', [status(thm)], ['29', '30', '33'])).
% 0.76/0.93  thf('35', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.76/0.93           = (k4_xboole_0 @ X2 @ 
% 0.76/0.93              (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))))),
% 0.76/0.93      inference('demod', [status(thm)], ['28', '34'])).
% 0.76/0.93  thf('36', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.93           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['14', '15'])).
% 0.76/0.93  thf('37', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ X0)
% 0.76/0.93           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['35', '36'])).
% 0.76/0.93  thf('38', plain,
% 0.76/0.93      (![X22 : $i, X23 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.76/0.93           = (k4_xboole_0 @ X22 @ X23))),
% 0.76/0.93      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.76/0.93  thf('39', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.76/0.93           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['37', '38'])).
% 0.76/0.93  thf('40', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/0.93  thf('41', plain,
% 0.76/0.93      (![X24 : $i, X25 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.76/0.93           = (k3_xboole_0 @ X24 @ X25))),
% 0.76/0.93      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.76/0.93  thf('42', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/0.93  thf('43', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X0 @ X0)
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.76/0.93  thf('44', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.76/0.93  thf('45', plain,
% 0.76/0.93      (![X0 : $i]: ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['43', '44'])).
% 0.76/0.93  thf('46', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.76/0.93           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.76/0.93  thf('47', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['39', '40', '45', '46'])).
% 0.76/0.93  thf('48', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['23', '47'])).
% 0.76/0.93  thf('49', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.76/0.93          | (r2_hidden @ X0 @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['13', '48'])).
% 0.76/0.93  thf('50', plain,
% 0.76/0.93      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.76/0.93         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf('51', plain,
% 0.76/0.93      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.76/0.93       ((r2_hidden @ sk_B @ sk_A))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf('52', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.76/0.93      inference('sat_resolution*', [status(thm)], ['2', '9', '51'])).
% 0.76/0.93  thf('53', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.76/0.93      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.76/0.93  thf('54', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.76/0.93      inference('sup-', [status(thm)], ['49', '53'])).
% 0.76/0.93  thf('55', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.76/0.93      inference('simplify', [status(thm)], ['54'])).
% 0.76/0.93  thf('56', plain, ($false), inference('demod', [status(thm)], ['11', '55'])).
% 0.76/0.93  
% 0.76/0.93  % SZS output end Refutation
% 0.76/0.93  
% 0.76/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
