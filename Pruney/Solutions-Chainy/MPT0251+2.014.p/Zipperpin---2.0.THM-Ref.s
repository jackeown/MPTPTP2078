%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJ6j1Sohqj

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:03 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 123 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  562 ( 827 expanded)
%              Number of equality atoms :   54 (  83 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
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

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

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

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X39 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','47'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X37 @ X38 ) )
      = ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CJ6j1Sohqj
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 380 iterations in 0.133s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(d4_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.36/0.60       ( ![D:$i]:
% 0.36/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.36/0.60         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.36/0.60          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.36/0.60          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('1', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf(t28_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.60  thf('4', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf(t100_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X17 @ X18)
% 0.36/0.60           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '6'])).
% 0.36/0.60  thf(d5_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.36/0.60       ( ![D:$i]:
% 0.36/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X12 @ X11)
% 0.36/0.60          | ~ (r2_hidden @ X12 @ X10)
% 0.36/0.60          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X12 @ X10)
% 0.36/0.60          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.36/0.60          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '9'])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X6 @ X5)
% 0.36/0.60          | (r2_hidden @ X6 @ X4)
% 0.36/0.60          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.36/0.60         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.36/0.60  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.36/0.60      inference('clc', [status(thm)], ['10', '14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.60          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['0', '15'])).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 0.36/0.60          | ((X1) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.60  thf(t46_zfmisc_1, conjecture,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.60       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i,B:$i]:
% 0.36/0.60        ( ( r2_hidden @ A @ B ) =>
% 0.36/0.60          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.36/0.60  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t38_zfmisc_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.36/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.36/0.60  thf('21', plain,
% 0.36/0.60      (![X39 : $i, X41 : $i, X42 : $i]:
% 0.36/0.60         ((r1_tarski @ (k2_tarski @ X39 @ X41) @ X42)
% 0.36/0.60          | ~ (r2_hidden @ X41 @ X42)
% 0.36/0.60          | ~ (r2_hidden @ X39 @ X42))),
% 0.36/0.60      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X0 @ sk_B)
% 0.36/0.60          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.60  thf('23', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B)),
% 0.36/0.60      inference('sup-', [status(thm)], ['19', '22'])).
% 0.36/0.60  thf(t69_enumset1, axiom,
% 0.36/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.36/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.60  thf('25', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X17 @ X18)
% 0.36/0.60           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X0 @ X1)
% 0.36/0.60           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.36/0.60         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['29', '32'])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('35', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.36/0.60      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      (![X20 : $i, X21 : $i]:
% 0.36/0.60         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.36/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.60  thf('37', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X17 @ X18)
% 0.36/0.60           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X12 @ X11)
% 0.36/0.60          | (r2_hidden @ X12 @ X9)
% 0.36/0.60          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.36/0.60         ((r2_hidden @ X12 @ X9)
% 0.36/0.60          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['40'])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['39', '41'])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('sup+', [status(thm)], ['37', '38'])).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X12 @ X10)
% 0.36/0.60          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.36/0.60      inference('simplify', [status(thm)], ['8'])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.36/0.60          | ~ (r2_hidden @ X1 @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.36/0.60      inference('clc', [status(thm)], ['42', '45'])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.36/0.60      inference('sup-', [status(thm)], ['33', '46'])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['18', '47'])).
% 0.36/0.60  thf(t39_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X23 : $i, X24 : $i]:
% 0.36/0.60         ((k2_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23))
% 0.36/0.60           = (k2_xboole_0 @ X23 @ X24))),
% 0.36/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.36/0.60         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['48', '49'])).
% 0.36/0.60  thf(t1_boole, axiom,
% 0.36/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.60  thf('51', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.36/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.36/0.60  thf('52', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['50', '51'])).
% 0.36/0.60  thf('53', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(commutativity_k2_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.60  thf('54', plain,
% 0.36/0.60      (![X25 : $i, X26 : $i]:
% 0.36/0.60         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.60  thf(l51_zfmisc_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('55', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i]:
% 0.36/0.60         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.36/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.60  thf('56', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.60  thf('57', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i]:
% 0.36/0.60         ((k3_tarski @ (k2_tarski @ X37 @ X38)) = (k2_xboole_0 @ X37 @ X38))),
% 0.36/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.60  thf('58', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('sup+', [status(thm)], ['56', '57'])).
% 0.36/0.60  thf('59', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.36/0.60      inference('demod', [status(thm)], ['53', '58'])).
% 0.36/0.60  thf('60', plain, ($false),
% 0.36/0.60      inference('simplify_reflect-', [status(thm)], ['52', '59'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
