%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pG0x0PzoVt

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:07 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 138 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  524 ( 879 expanded)
%              Number of equality atoms :   58 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X37 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r2_hidden @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','26'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('48',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('49',plain,
    ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','50'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','51'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pG0x0PzoVt
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.39/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.55  % Solved by: fo/fo7.sh
% 0.39/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.55  % done 285 iterations in 0.107s
% 0.39/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.55  % SZS output start Refutation
% 0.39/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.55  thf(t46_zfmisc_1, conjecture,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.55       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.39/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.55    (~( ![A:$i,B:$i]:
% 0.39/0.55        ( ( r2_hidden @ A @ B ) =>
% 0.39/0.55          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.39/0.55    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.39/0.55  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf(t38_zfmisc_1, axiom,
% 0.39/0.55    (![A:$i,B:$i,C:$i]:
% 0.39/0.55     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.39/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.39/0.55  thf('2', plain,
% 0.39/0.55      (![X37 : $i, X39 : $i, X40 : $i]:
% 0.39/0.55         ((r1_tarski @ (k2_tarski @ X37 @ X39) @ X40)
% 0.39/0.55          | ~ (r2_hidden @ X39 @ X40)
% 0.39/0.55          | ~ (r2_hidden @ X37 @ X40))),
% 0.39/0.55      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.39/0.55  thf('3', plain,
% 0.39/0.55      (![X0 : $i]:
% 0.39/0.55         (~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.55          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.39/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.55  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.39/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.55  thf(t69_enumset1, axiom,
% 0.39/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.55  thf('5', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.39/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.55  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.55  thf(t28_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.55  thf('7', plain,
% 0.39/0.55      (![X16 : $i, X17 : $i]:
% 0.39/0.55         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.39/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.55  thf('8', plain,
% 0.39/0.55      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.39/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.55  thf(t100_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.55  thf('9', plain,
% 0.39/0.55      (![X13 : $i, X14 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ X13 @ X14)
% 0.39/0.55           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.39/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.55  thf('10', plain,
% 0.39/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.39/0.55         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.39/0.55      inference('sup+', [status(thm)], ['8', '9'])).
% 0.39/0.55  thf(commutativity_k2_tarski, axiom,
% 0.39/0.55    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.55  thf('11', plain,
% 0.39/0.55      (![X23 : $i, X24 : $i]:
% 0.39/0.55         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.39/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.55  thf(l51_zfmisc_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.55  thf('12', plain,
% 0.39/0.55      (![X35 : $i, X36 : $i]:
% 0.39/0.55         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.39/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.55  thf('13', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]:
% 0.39/0.55         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.55      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.55  thf('14', plain,
% 0.39/0.55      (![X35 : $i, X36 : $i]:
% 0.39/0.55         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.39/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.55  thf('15', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.55  thf(t1_boole, axiom,
% 0.39/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.55  thf('16', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.39/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.55  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.55  thf(t40_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.55  thf('18', plain,
% 0.39/0.55      (![X20 : $i, X21 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ X21)
% 0.39/0.55           = (k4_xboole_0 @ X20 @ X21))),
% 0.39/0.55      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.55  thf('19', plain,
% 0.39/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.55  thf(d10_xboole_0, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.55  thf('20', plain,
% 0.39/0.55      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.39/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.55  thf('21', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.39/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.39/0.55  thf('22', plain,
% 0.39/0.55      (![X16 : $i, X17 : $i]:
% 0.39/0.55         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.39/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.55  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.55  thf('24', plain,
% 0.39/0.55      (![X13 : $i, X14 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ X13 @ X14)
% 0.39/0.55           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.39/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.55  thf('25', plain,
% 0.39/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.55  thf('26', plain,
% 0.39/0.55      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.55      inference('demod', [status(thm)], ['19', '25'])).
% 0.39/0.55  thf('27', plain,
% 0.39/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.39/0.55         = (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A)))),
% 0.39/0.55      inference('demod', [status(thm)], ['10', '26'])).
% 0.39/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.55  thf('28', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.39/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.55  thf(d3_tarski, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.55  thf('29', plain,
% 0.39/0.55      (![X1 : $i, X3 : $i]:
% 0.39/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.39/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.55  thf('30', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.55  thf(t4_xboole_0, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.55            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.55  thf('31', plain,
% 0.39/0.55      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.39/0.55         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.39/0.55          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.39/0.55      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.55  thf('32', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]:
% 0.39/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.55  thf('33', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['29', '32'])).
% 0.39/0.55  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.55      inference('sup-', [status(thm)], ['28', '33'])).
% 0.39/0.55  thf('35', plain,
% 0.39/0.55      (![X16 : $i, X17 : $i]:
% 0.39/0.55         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.39/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.55  thf('36', plain,
% 0.39/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.55  thf('37', plain,
% 0.39/0.55      (![X13 : $i, X14 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ X13 @ X14)
% 0.39/0.55           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.39/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.55  thf('38', plain,
% 0.39/0.55      (![X0 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.39/0.55           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.39/0.55  thf('39', plain,
% 0.39/0.55      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.39/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.55  thf('40', plain,
% 0.39/0.55      (![X35 : $i, X36 : $i]:
% 0.39/0.55         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.39/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.55  thf('41', plain,
% 0.39/0.55      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.39/0.55  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.39/0.55  thf(t39_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.55  thf('43', plain,
% 0.39/0.55      (![X18 : $i, X19 : $i]:
% 0.39/0.55         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.39/0.55           = (k2_xboole_0 @ X18 @ X19))),
% 0.39/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.55  thf('44', plain,
% 0.39/0.55      (![X0 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['42', '43'])).
% 0.39/0.55  thf('45', plain,
% 0.39/0.55      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.39/0.55         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 0.39/0.55      inference('sup+', [status(thm)], ['41', '44'])).
% 0.39/0.55  thf('46', plain,
% 0.39/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['23', '24'])).
% 0.39/0.55  thf('47', plain,
% 0.39/0.55      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.39/0.55  thf('48', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.39/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.55  thf('49', plain, (((k3_tarski @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 0.39/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.39/0.55  thf('50', plain,
% 0.39/0.55      (((k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.55      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.39/0.55  thf('51', plain,
% 0.39/0.55      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.55      inference('demod', [status(thm)], ['38', '50'])).
% 0.39/0.55  thf('52', plain,
% 0.39/0.55      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.39/0.55      inference('demod', [status(thm)], ['27', '51'])).
% 0.39/0.55  thf('53', plain,
% 0.39/0.55      (![X18 : $i, X19 : $i]:
% 0.39/0.55         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.39/0.55           = (k2_xboole_0 @ X18 @ X19))),
% 0.39/0.55      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.55  thf('54', plain,
% 0.39/0.55      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.39/0.55         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.55      inference('sup+', [status(thm)], ['52', '53'])).
% 0.39/0.55  thf('55', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.39/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.55  thf('56', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.39/0.55  thf('57', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.39/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.55  thf('58', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.55      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.55  thf('59', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.39/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.39/0.55  thf('60', plain, ($false),
% 0.39/0.55      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.39/0.55  
% 0.39/0.55  % SZS output end Refutation
% 0.39/0.55  
% 0.39/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
