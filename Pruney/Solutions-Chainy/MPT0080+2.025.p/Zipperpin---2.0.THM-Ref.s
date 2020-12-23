%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nD2zvzlevt

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 102 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  475 ( 629 expanded)
%              Number of equality atoms :   49 (  65 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k4_xboole_0 @ X26 @ ( k4_xboole_0 @ X26 @ X27 ) )
      = ( k3_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['3','23'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('26',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k4_xboole_0 @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['24','35'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('44',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nD2zvzlevt
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 175 iterations in 0.069s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(t73_xboole_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.20/0.51       ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ C ) ) =>
% 0.20/0.51          ( r1_tarski @ A @ B ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.20/0.51  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t12_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.20/0.51         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(t3_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('4', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf(t48_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X26 @ (k4_xboole_0 @ X26 @ X27))
% 0.20/0.51           = (k3_xboole_0 @ X26 @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t2_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(t41_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.51       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.20/0.51           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.51           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf(d7_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X6 : $i, X8 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.51  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf(t47_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25))
% 0.20/0.51           = (k4_xboole_0 @ X24 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.51           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '23'])).
% 0.20/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.51  thf('26', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.51  thf('28', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25))
% 0.20/0.51           = (k4_xboole_0 @ X24 @ X25))),
% 0.20/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.20/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf('32', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.20/0.51      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X23)
% 0.20/0.51           = (k4_xboole_0 @ X21 @ (k2_xboole_0 @ X22 @ X23)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ sk_A @ X0)
% 0.20/0.51           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ sk_A @ X0)
% 0.20/0.51           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_2)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['25', '34'])).
% 0.20/0.51  thf('36', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '35'])).
% 0.20/0.51  thf(t39_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.20/0.51           = (k2_xboole_0 @ X18 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf(t4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('41', plain,
% 0.20/0.52      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.20/0.52          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.52  thf('44', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.52  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['38', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.52  thf(t7_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.52      inference('sup+', [status(thm)], ['50', '53'])).
% 0.20/0.52  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
