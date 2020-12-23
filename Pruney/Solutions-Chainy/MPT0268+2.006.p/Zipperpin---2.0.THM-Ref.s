%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vtE9xJNVvn

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 141 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  541 (1048 expanded)
%              Number of equality atoms :   56 ( 104 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X28 @ X29 ) @ X29 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

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

thf('8',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_A @ X0 )
        | ~ ( r2_hidden @ sk_B_1 @ X0 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X42: $i] :
      ( ( k2_tarski @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( r2_hidden @ X58 @ X59 )
      | ~ ( r1_tarski @ ( k2_tarski @ X58 @ X60 ) @ X59 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['10','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X23 @ X24 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('21',plain,(
    ! [X52: $i,X53: $i] :
      ( ( X53
        = ( k1_tarski @ X52 ) )
      | ( X53 = k1_xboole_0 )
      | ~ ( r1_tarski @ X53 @ ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X16: $i,X18: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X18 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','29','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ( ( k4_xboole_0 @ X16 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X27: $i] :
      ( ( k5_xboole_0 @ X27 @ k1_xboole_0 )
      = X27 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('49',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','17','48'])).

thf('50',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['47','49'])).

thf('51',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['19','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vtE9xJNVvn
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.85/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.08  % Solved by: fo/fo7.sh
% 0.85/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.08  % done 1349 iterations in 0.635s
% 0.85/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.08  % SZS output start Refutation
% 0.85/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.85/1.08  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.85/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.08  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.85/1.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.08  thf(t65_zfmisc_1, conjecture,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.85/1.08       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.85/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.08    (~( ![A:$i,B:$i]:
% 0.85/1.08        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.85/1.08          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.85/1.08    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.85/1.08  thf('0', plain,
% 0.85/1.08      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.85/1.08        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.85/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.08  thf('1', plain,
% 0.85/1.08      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.85/1.08      inference('split', [status(esa)], ['0'])).
% 0.85/1.08  thf('2', plain,
% 0.85/1.08      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.85/1.08       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.85/1.08      inference('split', [status(esa)], ['0'])).
% 0.85/1.08  thf('3', plain,
% 0.85/1.08      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 0.85/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.85/1.08      inference('split', [status(esa)], ['0'])).
% 0.85/1.08  thf(t79_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.85/1.08  thf('4', plain,
% 0.85/1.08      (![X28 : $i, X29 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X28 @ X29) @ X29)),
% 0.85/1.08      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.85/1.08  thf('5', plain,
% 0.85/1.08      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.85/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.85/1.08      inference('sup+', [status(thm)], ['3', '4'])).
% 0.85/1.08  thf('6', plain,
% 0.85/1.08      (((r2_hidden @ sk_B_1 @ sk_A)
% 0.85/1.08        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 0.85/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.08  thf('7', plain,
% 0.85/1.08      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.85/1.08      inference('split', [status(esa)], ['6'])).
% 0.85/1.08  thf(t3_xboole_0, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.85/1.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.85/1.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.85/1.08  thf('8', plain,
% 0.85/1.08      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.85/1.08         (~ (r2_hidden @ X10 @ X8)
% 0.85/1.08          | ~ (r2_hidden @ X10 @ X11)
% 0.85/1.08          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.85/1.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.85/1.08  thf('9', plain,
% 0.85/1.08      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_A @ X0) | ~ (r2_hidden @ sk_B_1 @ X0)))
% 0.85/1.08         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.85/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.85/1.08  thf('10', plain,
% 0.85/1.08      ((~ (r2_hidden @ sk_B_1 @ (k1_tarski @ sk_B_1)))
% 0.85/1.08         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.85/1.08             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.85/1.08      inference('sup-', [status(thm)], ['5', '9'])).
% 0.85/1.08  thf(d10_xboole_0, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.08  thf('11', plain,
% 0.85/1.08      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.85/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.08  thf('12', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.85/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.85/1.08  thf(t69_enumset1, axiom,
% 0.85/1.08    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.85/1.08  thf('13', plain,
% 0.85/1.08      (![X42 : $i]: ((k2_tarski @ X42 @ X42) = (k1_tarski @ X42))),
% 0.85/1.08      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.85/1.08  thf(t38_zfmisc_1, axiom,
% 0.85/1.08    (![A:$i,B:$i,C:$i]:
% 0.85/1.08     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.85/1.08       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.85/1.08  thf('14', plain,
% 0.85/1.08      (![X58 : $i, X59 : $i, X60 : $i]:
% 0.85/1.08         ((r2_hidden @ X58 @ X59)
% 0.85/1.08          | ~ (r1_tarski @ (k2_tarski @ X58 @ X60) @ X59))),
% 0.85/1.08      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.85/1.08  thf('15', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.85/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.08  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['12', '15'])).
% 0.85/1.08  thf('17', plain,
% 0.85/1.08      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 0.85/1.08       ~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.85/1.08      inference('demod', [status(thm)], ['10', '16'])).
% 0.85/1.08  thf('18', plain, (~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.85/1.08      inference('sat_resolution*', [status(thm)], ['2', '17'])).
% 0.85/1.08  thf('19', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 0.85/1.08      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.85/1.08  thf(t36_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.08  thf('20', plain,
% 0.85/1.08      (![X23 : $i, X24 : $i]: (r1_tarski @ (k4_xboole_0 @ X23 @ X24) @ X23)),
% 0.85/1.08      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.08  thf(l3_zfmisc_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.85/1.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.85/1.08  thf('21', plain,
% 0.85/1.08      (![X52 : $i, X53 : $i]:
% 0.85/1.08         (((X53) = (k1_tarski @ X52))
% 0.85/1.08          | ((X53) = (k1_xboole_0))
% 0.85/1.08          | ~ (r1_tarski @ X53 @ (k1_tarski @ X52)))),
% 0.85/1.08      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.85/1.08  thf('22', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.85/1.08          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.85/1.08      inference('sup-', [status(thm)], ['20', '21'])).
% 0.85/1.08  thf(t48_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.85/1.08  thf('23', plain,
% 0.85/1.08      (![X25 : $i, X26 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.85/1.08           = (k3_xboole_0 @ X25 @ X26))),
% 0.85/1.08      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.85/1.08  thf('24', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.85/1.08            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.85/1.08          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['22', '23'])).
% 0.85/1.08  thf('25', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.85/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.85/1.08  thf(t28_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.85/1.08  thf('26', plain,
% 0.85/1.08      (![X21 : $i, X22 : $i]:
% 0.85/1.08         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.85/1.08      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.85/1.08  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['25', '26'])).
% 0.85/1.08  thf(t100_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.08  thf('28', plain,
% 0.85/1.08      (![X19 : $i, X20 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X19 @ X20)
% 0.85/1.08           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.08  thf('29', plain,
% 0.85/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['27', '28'])).
% 0.85/1.08  thf('30', plain,
% 0.85/1.08      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['27', '28'])).
% 0.85/1.08  thf('31', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.85/1.08      inference('simplify', [status(thm)], ['11'])).
% 0.85/1.08  thf(l32_xboole_1, axiom,
% 0.85/1.08    (![A:$i,B:$i]:
% 0.85/1.08     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.85/1.08  thf('32', plain,
% 0.85/1.08      (![X16 : $i, X18 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ X16 @ X18) = (k1_xboole_0))
% 0.85/1.08          | ~ (r1_tarski @ X16 @ X18))),
% 0.85/1.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.85/1.08  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['31', '32'])).
% 0.85/1.08  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['30', '33'])).
% 0.85/1.08  thf('35', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.85/1.08          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.85/1.08      inference('demod', [status(thm)], ['24', '29', '34'])).
% 0.85/1.08  thf('36', plain,
% 0.85/1.08      (![X16 : $i, X17 : $i]:
% 0.85/1.08         ((r1_tarski @ X16 @ X17)
% 0.85/1.08          | ((k4_xboole_0 @ X16 @ X17) != (k1_xboole_0)))),
% 0.85/1.08      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.85/1.08  thf('37', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k1_xboole_0) != (k1_xboole_0))
% 0.85/1.08          | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.85/1.08          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['35', '36'])).
% 0.85/1.08  thf('38', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((r1_tarski @ (k1_tarski @ X1) @ X0)
% 0.85/1.08          | ((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.85/1.08      inference('simplify', [status(thm)], ['37'])).
% 0.85/1.08  thf('39', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.85/1.08      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.08  thf('40', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.85/1.08          | (r2_hidden @ X1 @ X0))),
% 0.85/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.85/1.08  thf(commutativity_k3_xboole_0, axiom,
% 0.85/1.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.85/1.08  thf('41', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.85/1.08      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.85/1.08  thf('42', plain,
% 0.85/1.08      (![X19 : $i, X20 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X19 @ X20)
% 0.85/1.08           = (k5_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.85/1.08      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.08  thf('43', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         ((k4_xboole_0 @ X0 @ X1)
% 0.85/1.08           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.85/1.08      inference('sup+', [status(thm)], ['41', '42'])).
% 0.85/1.08  thf('44', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.85/1.08            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.85/1.08          | (r2_hidden @ X1 @ X0))),
% 0.85/1.08      inference('sup+', [status(thm)], ['40', '43'])).
% 0.85/1.08  thf(t5_boole, axiom,
% 0.85/1.08    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.08  thf('45', plain, (![X27 : $i]: ((k5_xboole_0 @ X27 @ k1_xboole_0) = (X27))),
% 0.85/1.08      inference('cnf', [status(esa)], [t5_boole])).
% 0.85/1.08  thf('46', plain,
% 0.85/1.08      (![X0 : $i, X1 : $i]:
% 0.85/1.08         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.85/1.08          | (r2_hidden @ X1 @ X0))),
% 0.85/1.08      inference('demod', [status(thm)], ['44', '45'])).
% 0.85/1.08  thf('47', plain,
% 0.85/1.08      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 0.85/1.08         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.85/1.08      inference('split', [status(esa)], ['6'])).
% 0.85/1.08  thf('48', plain,
% 0.85/1.08      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 0.85/1.08       ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.85/1.08      inference('split', [status(esa)], ['6'])).
% 0.85/1.08  thf('49', plain,
% 0.85/1.08      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.85/1.08      inference('sat_resolution*', [status(thm)], ['2', '17', '48'])).
% 0.85/1.08  thf('50', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A))),
% 0.85/1.08      inference('simpl_trail', [status(thm)], ['47', '49'])).
% 0.85/1.08  thf('51', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.85/1.08      inference('sup-', [status(thm)], ['46', '50'])).
% 0.85/1.08  thf('52', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.85/1.08      inference('simplify', [status(thm)], ['51'])).
% 0.85/1.08  thf('53', plain, ($false), inference('demod', [status(thm)], ['19', '52'])).
% 0.85/1.08  
% 0.85/1.08  % SZS output end Refutation
% 0.85/1.08  
% 0.91/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
