%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.je3Afq5N2L

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:10 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 132 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  527 ( 889 expanded)
%              Number of equality atoms :   56 (  89 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X43: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X41 ) @ X43 )
      | ~ ( r2_hidden @ X41 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X23: $i] :
      ( ( k2_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X29 @ X30 ) @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ( X18 != X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,(
    ! [X19: $i] :
      ( r1_tarski @ X19 @ X19 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X16 )
      | ~ ( r2_hidden @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ k1_xboole_0 )
      = X28 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','21','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','49'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X26 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k2_xboole_0 @ X23 @ k1_xboole_0 )
      = X23 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('54',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('57',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.je3Afq5N2L
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.63  % Solved by: fo/fo7.sh
% 0.37/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.63  % done 449 iterations in 0.177s
% 0.37/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.63  % SZS output start Refutation
% 0.37/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.63  thf(t46_zfmisc_1, conjecture,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r2_hidden @ A @ B ) =>
% 0.37/0.63       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i,B:$i]:
% 0.37/0.63        ( ( r2_hidden @ A @ B ) =>
% 0.37/0.63          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.37/0.63  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf(l1_zfmisc_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.37/0.63  thf('1', plain,
% 0.37/0.63      (![X41 : $i, X43 : $i]:
% 0.37/0.63         ((r1_tarski @ (k1_tarski @ X41) @ X43) | ~ (r2_hidden @ X41 @ X43))),
% 0.37/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.37/0.63  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.37/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.63  thf(t28_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.63  thf('3', plain,
% 0.37/0.63      (![X24 : $i, X25 : $i]:
% 0.37/0.63         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.37/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.63  thf('4', plain,
% 0.37/0.63      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.63  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.63  thf('5', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf('6', plain,
% 0.37/0.63      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.37/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.37/0.63  thf('7', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf(t100_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.63  thf('8', plain,
% 0.37/0.63      (![X21 : $i, X22 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.37/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ X1)
% 0.37/0.63           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['7', '8'])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.37/0.63         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['6', '9'])).
% 0.37/0.63  thf(commutativity_k2_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf(t1_boole, axiom,
% 0.37/0.63    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.63  thf('12', plain, (![X23 : $i]: ((k2_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.37/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.63  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['11', '12'])).
% 0.37/0.63  thf(t40_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (![X29 : $i, X30 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X29 @ X30) @ X30)
% 0.37/0.63           = (k4_xboole_0 @ X29 @ X30))),
% 0.37/0.63      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.37/0.63  thf('15', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['13', '14'])).
% 0.37/0.63  thf(d10_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      (![X18 : $i, X19 : $i]: ((r1_tarski @ X18 @ X19) | ((X18) != (X19)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.63  thf('17', plain, (![X19 : $i]: (r1_tarski @ X19 @ X19)),
% 0.37/0.63      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X24 : $i, X25 : $i]:
% 0.37/0.63         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.37/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.63  thf('19', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X21 : $i, X22 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.37/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['19', '20'])).
% 0.37/0.63  thf(d3_tarski, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (![X5 : $i, X7 : $i]:
% 0.37/0.63         ((r1_tarski @ X5 @ X7) | (r2_hidden @ (sk_C @ X7 @ X5) @ X5))),
% 0.37/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.63  thf(t3_boole, axiom,
% 0.37/0.63    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.63  thf('23', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.63  thf('24', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.63  thf('25', plain,
% 0.37/0.63      (![X21 : $i, X22 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.37/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf(t1_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.63       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X14 @ X15)
% 0.37/0.63          | ~ (r2_hidden @ X14 @ X16)
% 0.37/0.63          | ~ (r2_hidden @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X2 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf(d4_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i,C:$i]:
% 0.37/0.63     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.37/0.63       ( ![D:$i]:
% 0.37/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.63           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X12 @ X11)
% 0.37/0.63          | (r2_hidden @ X12 @ X10)
% 0.37/0.63          | ((X11) != (k3_xboole_0 @ X9 @ X10)))),
% 0.37/0.63      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.37/0.63  thf('30', plain,
% 0.37/0.63      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.37/0.63         ((r2_hidden @ X12 @ X10)
% 0.37/0.63          | ~ (r2_hidden @ X12 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.37/0.63      inference('sup-', [status(thm)], ['28', '30'])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.37/0.63          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['27', '31'])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X1 @ X0)
% 0.37/0.63          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['24', '32'])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['23', '33'])).
% 0.37/0.63  thf('35', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.63      inference('simplify', [status(thm)], ['34'])).
% 0.37/0.63  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.63      inference('sup-', [status(thm)], ['22', '35'])).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      (![X24 : $i, X25 : $i]:
% 0.37/0.63         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.37/0.63      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (![X21 : $i, X22 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.37/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.63           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.63  thf('42', plain,
% 0.37/0.63      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.63  thf('44', plain,
% 0.37/0.63      (![X21 : $i, X22 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X21 @ X22)
% 0.37/0.63           = (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.63  thf('45', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.63  thf('46', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ k1_xboole_0) = (X28))),
% 0.37/0.63      inference('cnf', [status(esa)], [t3_boole])).
% 0.37/0.63  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['45', '46'])).
% 0.37/0.63  thf('48', plain,
% 0.37/0.63      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['40', '47'])).
% 0.37/0.63  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['15', '21', '48'])).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.37/0.63      inference('demod', [status(thm)], ['10', '49'])).
% 0.37/0.63  thf(t39_xboole_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      (![X26 : $i, X27 : $i]:
% 0.37/0.63         ((k2_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X26))
% 0.37/0.63           = (k2_xboole_0 @ X26 @ X27))),
% 0.37/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      (((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.37/0.63         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['50', '51'])).
% 0.37/0.63  thf('53', plain, (![X23 : $i]: ((k2_xboole_0 @ X23 @ k1_xboole_0) = (X23))),
% 0.37/0.63      inference('cnf', [status(esa)], [t1_boole])).
% 0.37/0.63  thf('54', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.63  thf('55', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.37/0.63      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.37/0.63  thf('57', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.37/0.63      inference('demod', [status(thm)], ['55', '56'])).
% 0.37/0.63  thf('58', plain, ($false),
% 0.37/0.63      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
