%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a53tv5ZZp5

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:32 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 126 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  503 ( 890 expanded)
%              Number of equality atoms :   44 (  83 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
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
    ! [X45: $i,X47: $i,X48: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X45 @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X45 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('6',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B ),
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
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C_1 ) ),
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
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

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

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','37'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('40',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_1 ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X43 @ X44 ) )
      = ( k2_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k2_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C_1 ) )
 != sk_B ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a53tv5ZZp5
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 804 iterations in 0.348s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.59/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(t48_zfmisc_1, conjecture,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.59/0.79       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.79        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.59/0.79          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 0.59/0.79  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t38_zfmisc_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.59/0.79       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X45 : $i, X47 : $i, X48 : $i]:
% 0.59/0.79         ((r1_tarski @ (k2_tarski @ X45 @ X47) @ X48)
% 0.59/0.79          | ~ (r2_hidden @ X47 @ X48)
% 0.59/0.79          | ~ (r2_hidden @ X45 @ X48))),
% 0.59/0.79      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ sk_B)
% 0.59/0.79          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.79  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_A) @ sk_B)),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '3'])).
% 0.59/0.79  thf(commutativity_k2_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i]:
% 0.59/0.79         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.79  thf('6', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.79  thf(t28_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.59/0.79         = (k2_tarski @ sk_A @ sk_C_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.79  thf(t100_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X13 @ X14)
% 0.59/0.79           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B)
% 0.59/0.79         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ 
% 0.59/0.79            (k2_tarski @ sk_A @ sk_C_1)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf(d5_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.59/0.79       ( ![D:$i]:
% 0.59/0.79         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.79           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.59/0.79         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.59/0.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.59/0.79          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.79  thf(t5_boole, axiom,
% 0.59/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.79  thf('12', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.59/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('14', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.59/0.79      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i]:
% 0.59/0.79         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.59/0.79  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X13 : $i, X14 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X13 @ X14)
% 0.59/0.79           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.79          | ~ (r2_hidden @ X4 @ X2)
% 0.59/0.79          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X4 @ X2)
% 0.59/0.79          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.59/0.79          | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['12', '21'])).
% 0.59/0.80  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.59/0.80          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['11', '23'])).
% 0.59/0.80  thf(t3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X6 : $i, X7 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['22'])).
% 0.59/0.80  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.80  thf(t83_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X21 : $i, X22 : $i]:
% 0.59/0.80         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.59/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.59/0.80          | ((X1) = (k1_xboole_0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['24', '29'])).
% 0.59/0.80  thf('31', plain,
% 0.59/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X4 @ X3)
% 0.59/0.80          | (r2_hidden @ X4 @ X1)
% 0.59/0.80          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.59/0.80         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['32'])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['31', '33'])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.59/0.80          | ~ (r2_hidden @ X1 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['18', '20'])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('clc', [status(thm)], ['34', '35'])).
% 0.59/0.80  thf('37', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['30', '36'])).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) = (k1_xboole_0))),
% 0.59/0.80      inference('demod', [status(thm)], ['10', '37'])).
% 0.59/0.80  thf(t39_xboole_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X18 : $i, X19 : $i]:
% 0.59/0.80         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 0.59/0.80           = (k2_xboole_0 @ X18 @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.59/0.80         = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['38', '39'])).
% 0.59/0.80  thf(t1_boole, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.80  thf('41', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.59/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.80  thf('42', plain,
% 0.59/0.80      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)))),
% 0.59/0.80      inference('demod', [status(thm)], ['40', '41'])).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_1) @ sk_B) != (sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X27 : $i, X28 : $i]:
% 0.59/0.80         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.59/0.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.59/0.80  thf(l51_zfmisc_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf('45', plain,
% 0.59/0.80      (![X43 : $i, X44 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.59/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['44', '45'])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X43 : $i, X44 : $i]:
% 0.59/0.80         ((k3_tarski @ (k2_tarski @ X43 @ X44)) = (k2_xboole_0 @ X43 @ X44))),
% 0.59/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['46', '47'])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (((k2_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C_1)) != (sk_B))),
% 0.59/0.80      inference('demod', [status(thm)], ['43', '48'])).
% 0.59/0.80  thf('50', plain, ($false),
% 0.59/0.80      inference('simplify_reflect-', [status(thm)], ['42', '49'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
