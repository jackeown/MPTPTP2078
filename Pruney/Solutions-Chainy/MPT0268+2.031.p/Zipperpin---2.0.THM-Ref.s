%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t8hQVqaHJe

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:56 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 177 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  619 (1426 expanded)
%              Number of equality atoms :   66 ( 155 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X32 ) @ X31 )
        = X31 )
      | ~ ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','13'])).

thf('15',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('17',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
       != ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('19',plain,
    ( ( ( ( k4_xboole_0 @ sk_A @ sk_A )
       != ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != ( k1_tarski @ sk_B ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X35: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X35 ) @ X37 )
        = ( k1_tarski @ X35 ) )
      | ( r2_hidden @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41','50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('57',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','22','56'])).

thf('58',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['24','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t8hQVqaHJe
% 0.15/0.38  % Computer   : n024.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 10:40:36 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 1019 iterations in 0.469s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(t65_zfmisc_1, conjecture,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.77/0.96       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i,B:$i]:
% 0.77/0.96        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.77/0.96          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.77/0.96        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.77/0.96       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.77/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf(t48_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.96           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ sk_A)
% 0.77/0.96          = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))
% 0.77/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.96      inference('sup+', [status(thm)], ['3', '4'])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (((r2_hidden @ sk_B @ sk_A)
% 0.77/0.96        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf(l22_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r2_hidden @ A @ B ) =>
% 0.77/0.96       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X31 : $i, X32 : $i]:
% 0.77/0.96         (((k2_xboole_0 @ (k1_tarski @ X32) @ X31) = (X31))
% 0.77/0.96          | ~ (r2_hidden @ X32 @ X31))),
% 0.77/0.96      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf(t21_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      ((((k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tarski @ sk_B)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.77/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      ((((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ sk_A) = (k1_tarski @ sk_B)))
% 0.77/0.96         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.77/0.96             ((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['5', '13'])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (sk_A)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf(t40_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.77/0.96           = (k4_xboole_0 @ X10 @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ sk_A)
% 0.77/0.96          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf(l33_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.77/0.96       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.77/0.96  thf('18', plain,
% 0.77/0.96      (![X35 : $i, X36 : $i]:
% 0.77/0.96         (~ (r2_hidden @ X35 @ X36)
% 0.77/0.96          | ((k4_xboole_0 @ (k1_tarski @ X35) @ X36) != (k1_tarski @ X35)))),
% 0.77/0.96      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (((((k4_xboole_0 @ sk_A @ sk_A) != (k1_tarski @ sk_B))
% 0.77/0.96         | ~ (r2_hidden @ sk_B @ sk_A))) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_tarski @ sk_B)))
% 0.77/0.96         <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.77/0.96       ~ ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.96      inference('simplify_reflect-', [status(thm)], ['14', '21'])).
% 0.77/0.96  thf('23', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['2', '22'])).
% 0.77/0.96  thf('24', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (![X35 : $i, X37 : $i]:
% 0.77/0.96         (((k4_xboole_0 @ (k1_tarski @ X35) @ X37) = (k1_tarski @ X35))
% 0.77/0.96          | (r2_hidden @ X35 @ X37))),
% 0.77/0.96      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf(idempotence_k2_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.77/0.96  thf('27', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.96  thf(t31_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( r1_tarski @
% 0.77/0.96       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.77/0.96       ( k2_xboole_0 @ B @ C ) ))).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.96         (r1_tarski @ 
% 0.77/0.96          (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)) @ 
% 0.77/0.96          (k2_xboole_0 @ X8 @ X9))),
% 0.77/0.96      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['27', '28'])).
% 0.77/0.96  thf('30', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.77/0.96      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.77/0.96      inference('sup+', [status(thm)], ['26', '31'])).
% 0.77/0.96  thf(t12_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i]:
% 0.77/0.96         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.77/0.96      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.77/0.96           = (k4_xboole_0 @ X10 @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.96           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['35', '36'])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['34', '39'])).
% 0.77/0.96  thf(t49_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.77/0.96       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.77/0.96           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.77/0.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.96           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.77/0.96           = (k3_xboole_0 @ X18 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['42', '43'])).
% 0.77/0.96  thf('45', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.77/0.96      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.77/0.96  thf('47', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['45', '46'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X20 @ (k4_xboole_0 @ X21 @ X22))
% 0.77/0.96           = (k4_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22))),
% 0.77/0.96      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.77/0.96           = (k4_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['47', '48'])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.77/0.96           = (k4_xboole_0 @ X1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['44', '49'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.96  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['45', '46'])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['40', '41', '50', '51', '52'])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.77/0.96          | (r2_hidden @ X0 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['25', '53'])).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.77/0.96         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 0.77/0.96       ((r2_hidden @ sk_B @ sk_A))),
% 0.77/0.96      inference('split', [status(esa)], ['6'])).
% 0.77/0.96  thf('57', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['2', '22', '56'])).
% 0.77/0.96  thf('58', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.77/0.96  thf('59', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['54', '58'])).
% 0.77/0.96  thf('60', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.77/0.96      inference('simplify', [status(thm)], ['59'])).
% 0.77/0.96  thf('61', plain, ($false), inference('demod', [status(thm)], ['24', '60'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
