%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rT7Pg2oMDA

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:11 EST 2020

% Result     : Theorem 2.23s
% Output     : Refutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   75 (  93 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  666 ( 864 expanded)
%              Number of equality atoms :   49 (  71 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X17 ) @ X17 )
      = ( k4_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) )
        = X40 )
      | ( r2_hidden @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) )
        = X40 )
      | ( r2_hidden @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t147_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( A != B )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_zfmisc_1])).

thf('6',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_C )
      | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ ( k3_tarski @ ( k1_tarski @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ) )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','25'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('27',plain,(
    ! [X35: $i,X36: $i,X38: $i] :
      ( ( r2_hidden @ X35 @ ( k4_xboole_0 @ X36 @ ( k1_tarski @ X38 ) ) )
      | ( X35 = X38 )
      | ~ ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('30',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) )
        = X40 )
      | ( r2_hidden @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t87_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X21 ) @ X22 )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X22 ) @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t87_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_B ) )
 != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('44',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) )
     != ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k4_xboole_0 @ X40 @ ( k1_tarski @ X41 ) )
        = X40 )
      | ( r2_hidden @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('47',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['34','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rT7Pg2oMDA
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.23/2.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.23/2.40  % Solved by: fo/fo7.sh
% 2.23/2.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.23/2.40  % done 2401 iterations in 1.948s
% 2.23/2.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.23/2.40  % SZS output start Refutation
% 2.23/2.40  thf(sk_A_type, type, sk_A: $i).
% 2.23/2.40  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.23/2.40  thf(sk_B_type, type, sk_B: $i).
% 2.23/2.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.23/2.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.23/2.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.23/2.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.23/2.40  thf(sk_C_type, type, sk_C: $i).
% 2.23/2.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.23/2.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.23/2.40  thf(t40_xboole_1, axiom,
% 2.23/2.40    (![A:$i,B:$i]:
% 2.23/2.40     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 2.23/2.40  thf('0', plain,
% 2.23/2.40      (![X16 : $i, X17 : $i]:
% 2.23/2.40         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X17) @ X17)
% 2.23/2.40           = (k4_xboole_0 @ X16 @ X17))),
% 2.23/2.40      inference('cnf', [status(esa)], [t40_xboole_1])).
% 2.23/2.40  thf(t69_enumset1, axiom,
% 2.23/2.40    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.23/2.40  thf('1', plain, (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 2.23/2.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.23/2.40  thf(l51_zfmisc_1, axiom,
% 2.23/2.40    (![A:$i,B:$i]:
% 2.23/2.40     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.23/2.40  thf('2', plain,
% 2.23/2.40      (![X33 : $i, X34 : $i]:
% 2.23/2.40         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 2.23/2.40      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.23/2.40  thf('3', plain,
% 2.23/2.40      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 2.23/2.40      inference('sup+', [status(thm)], ['1', '2'])).
% 2.23/2.40  thf(t65_zfmisc_1, axiom,
% 2.23/2.40    (![A:$i,B:$i]:
% 2.23/2.40     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.23/2.40       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.23/2.40  thf('4', plain,
% 2.23/2.40      (![X40 : $i, X41 : $i]:
% 2.23/2.40         (((k4_xboole_0 @ X40 @ (k1_tarski @ X41)) = (X40))
% 2.23/2.40          | (r2_hidden @ X41 @ X40))),
% 2.23/2.40      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.23/2.40  thf('5', plain,
% 2.23/2.40      (![X40 : $i, X41 : $i]:
% 2.23/2.40         (((k4_xboole_0 @ X40 @ (k1_tarski @ X41)) = (X40))
% 2.23/2.40          | (r2_hidden @ X41 @ X40))),
% 2.23/2.40      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.23/2.40  thf(t147_zfmisc_1, conjecture,
% 2.23/2.40    (![A:$i,B:$i,C:$i]:
% 2.23/2.40     ( ( ( A ) != ( B ) ) =>
% 2.23/2.40       ( ( k4_xboole_0 @
% 2.23/2.40           ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 2.23/2.40         ( k2_xboole_0 @
% 2.23/2.40           ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ))).
% 2.23/2.40  thf(zf_stmt_0, negated_conjecture,
% 2.23/2.40    (~( ![A:$i,B:$i,C:$i]:
% 2.23/2.40        ( ( ( A ) != ( B ) ) =>
% 2.23/2.40          ( ( k4_xboole_0 @
% 2.23/2.40              ( k2_xboole_0 @ C @ ( k1_tarski @ A ) ) @ ( k1_tarski @ B ) ) =
% 2.23/2.40            ( k2_xboole_0 @
% 2.23/2.40              ( k4_xboole_0 @ C @ ( k1_tarski @ B ) ) @ ( k1_tarski @ A ) ) ) ) )),
% 2.23/2.40    inference('cnf.neg', [status(esa)], [t147_zfmisc_1])).
% 2.23/2.40  thf('6', plain,
% 2.23/2.40      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 2.23/2.40         (k1_tarski @ sk_B))
% 2.23/2.40         != (k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 2.23/2.40             (k1_tarski @ sk_A)))),
% 2.23/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.40  thf(commutativity_k2_xboole_0, axiom,
% 2.23/2.40    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.23/2.40  thf('7', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.23/2.40      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.23/2.40  thf('8', plain,
% 2.23/2.40      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 2.23/2.40         (k1_tarski @ sk_B))
% 2.23/2.40         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 2.23/2.40      inference('demod', [status(thm)], ['6', '7'])).
% 2.23/2.40  thf('9', plain,
% 2.23/2.40      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 2.23/2.40          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 2.23/2.40        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 2.23/2.40      inference('sup-', [status(thm)], ['5', '8'])).
% 2.23/2.40  thf('10', plain,
% 2.23/2.40      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 2.23/2.40          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C))
% 2.23/2.40        | (r2_hidden @ sk_B @ sk_C)
% 2.23/2.40        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 2.23/2.40      inference('sup-', [status(thm)], ['4', '9'])).
% 2.23/2.40  thf('11', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.23/2.40      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.23/2.40  thf('12', plain,
% 2.23/2.40      ((((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))
% 2.23/2.40          != (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 2.23/2.40        | (r2_hidden @ sk_B @ sk_C)
% 2.23/2.40        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 2.23/2.40      inference('demod', [status(thm)], ['10', '11'])).
% 2.23/2.40  thf('13', plain,
% 2.23/2.40      (((r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 2.23/2.40        | (r2_hidden @ sk_B @ sk_C))),
% 2.23/2.40      inference('simplify', [status(thm)], ['12'])).
% 2.23/2.40  thf(d3_xboole_0, axiom,
% 2.23/2.40    (![A:$i,B:$i,C:$i]:
% 2.23/2.40     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.23/2.40       ( ![D:$i]:
% 2.23/2.40         ( ( r2_hidden @ D @ C ) <=>
% 2.23/2.40           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.23/2.40  thf('14', plain,
% 2.23/2.40      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X2 @ X3)
% 2.23/2.40          | (r2_hidden @ X2 @ X4)
% 2.23/2.40          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.23/2.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.23/2.40  thf('15', plain,
% 2.23/2.40      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.23/2.40         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 2.23/2.40      inference('simplify', [status(thm)], ['14'])).
% 2.23/2.40  thf('16', plain,
% 2.23/2.40      (![X0 : $i]:
% 2.23/2.40         ((r2_hidden @ sk_B @ sk_C)
% 2.23/2.40          | (r2_hidden @ sk_B @ 
% 2.23/2.40             (k2_xboole_0 @ X0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))))),
% 2.23/2.40      inference('sup-', [status(thm)], ['13', '15'])).
% 2.23/2.40  thf('17', plain,
% 2.23/2.40      (((r2_hidden @ sk_B @ 
% 2.23/2.40         (k3_tarski @ (k1_tarski @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))))
% 2.23/2.40        | (r2_hidden @ sk_B @ sk_C))),
% 2.23/2.40      inference('sup+', [status(thm)], ['3', '16'])).
% 2.23/2.40  thf('18', plain,
% 2.23/2.40      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 2.23/2.40      inference('sup+', [status(thm)], ['1', '2'])).
% 2.23/2.40  thf('19', plain,
% 2.23/2.40      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X6 @ X4)
% 2.23/2.40          | (r2_hidden @ X6 @ X5)
% 2.23/2.40          | (r2_hidden @ X6 @ X3)
% 2.23/2.40          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.23/2.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.23/2.40  thf('20', plain,
% 2.23/2.40      (![X3 : $i, X5 : $i, X6 : $i]:
% 2.23/2.40         ((r2_hidden @ X6 @ X3)
% 2.23/2.40          | (r2_hidden @ X6 @ X5)
% 2.23/2.40          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 2.23/2.40      inference('simplify', [status(thm)], ['19'])).
% 2.23/2.40  thf('21', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0)))
% 2.23/2.40          | (r2_hidden @ X1 @ X0)
% 2.23/2.40          | (r2_hidden @ X1 @ X0))),
% 2.23/2.40      inference('sup-', [status(thm)], ['18', '20'])).
% 2.23/2.40  thf('22', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         ((r2_hidden @ X1 @ X0)
% 2.23/2.40          | ~ (r2_hidden @ X1 @ (k3_tarski @ (k1_tarski @ X0))))),
% 2.23/2.40      inference('simplify', [status(thm)], ['21'])).
% 2.23/2.40  thf('23', plain,
% 2.23/2.40      (((r2_hidden @ sk_B @ sk_C)
% 2.23/2.40        | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 2.23/2.40      inference('sup-', [status(thm)], ['17', '22'])).
% 2.23/2.40  thf('24', plain,
% 2.23/2.40      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X2 @ X5)
% 2.23/2.40          | (r2_hidden @ X2 @ X4)
% 2.23/2.40          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 2.23/2.40      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.23/2.40  thf('25', plain,
% 2.23/2.40      (![X2 : $i, X3 : $i, X5 : $i]:
% 2.23/2.40         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 2.23/2.40      inference('simplify', [status(thm)], ['24'])).
% 2.23/2.40  thf('26', plain,
% 2.23/2.40      ((r2_hidden @ sk_B @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))),
% 2.23/2.40      inference('clc', [status(thm)], ['23', '25'])).
% 2.23/2.40  thf(t64_zfmisc_1, axiom,
% 2.23/2.40    (![A:$i,B:$i,C:$i]:
% 2.23/2.40     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 2.23/2.40       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 2.23/2.40  thf('27', plain,
% 2.23/2.40      (![X35 : $i, X36 : $i, X38 : $i]:
% 2.23/2.40         ((r2_hidden @ X35 @ (k4_xboole_0 @ X36 @ (k1_tarski @ X38)))
% 2.23/2.40          | ((X35) = (X38))
% 2.23/2.40          | ~ (r2_hidden @ X35 @ X36))),
% 2.23/2.40      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 2.23/2.40  thf('28', plain,
% 2.23/2.40      (![X0 : $i]:
% 2.23/2.40         (((sk_B) = (X0))
% 2.23/2.40          | (r2_hidden @ sk_B @ 
% 2.23/2.40             (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 2.23/2.40              (k1_tarski @ X0))))),
% 2.23/2.40      inference('sup-', [status(thm)], ['26', '27'])).
% 2.23/2.40  thf('29', plain,
% 2.23/2.40      (((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))
% 2.23/2.40        | ((sk_B) = (sk_A)))),
% 2.23/2.40      inference('sup+', [status(thm)], ['0', '28'])).
% 2.23/2.40  thf('30', plain, (((sk_A) != (sk_B))),
% 2.23/2.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.23/2.40  thf('31', plain,
% 2.23/2.40      ((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)))),
% 2.23/2.40      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 2.23/2.40  thf(d5_xboole_0, axiom,
% 2.23/2.40    (![A:$i,B:$i,C:$i]:
% 2.23/2.40     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.23/2.40       ( ![D:$i]:
% 2.23/2.40         ( ( r2_hidden @ D @ C ) <=>
% 2.23/2.40           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.23/2.40  thf('32', plain,
% 2.23/2.40      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X12 @ X11)
% 2.23/2.40          | ~ (r2_hidden @ X12 @ X10)
% 2.23/2.40          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 2.23/2.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.23/2.40  thf('33', plain,
% 2.23/2.40      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X12 @ X10)
% 2.23/2.40          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.23/2.40      inference('simplify', [status(thm)], ['32'])).
% 2.23/2.40  thf('34', plain, (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 2.23/2.40      inference('sup-', [status(thm)], ['31', '33'])).
% 2.23/2.40  thf('35', plain,
% 2.23/2.40      (![X40 : $i, X41 : $i]:
% 2.23/2.40         (((k4_xboole_0 @ X40 @ (k1_tarski @ X41)) = (X40))
% 2.23/2.40          | (r2_hidden @ X41 @ X40))),
% 2.23/2.40      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.23/2.40  thf(t83_xboole_1, axiom,
% 2.23/2.40    (![A:$i,B:$i]:
% 2.23/2.40     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.23/2.40  thf('36', plain,
% 2.23/2.40      (![X18 : $i, X20 : $i]:
% 2.23/2.40         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 2.23/2.40      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.23/2.40  thf('37', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         (((X0) != (X0))
% 2.23/2.40          | (r2_hidden @ X1 @ X0)
% 2.23/2.40          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.23/2.40      inference('sup-', [status(thm)], ['35', '36'])).
% 2.23/2.40  thf('38', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 2.23/2.40      inference('simplify', [status(thm)], ['37'])).
% 2.23/2.40  thf(t87_xboole_1, axiom,
% 2.23/2.40    (![A:$i,B:$i,C:$i]:
% 2.23/2.40     ( ( r1_xboole_0 @ A @ B ) =>
% 2.23/2.40       ( ( k2_xboole_0 @ ( k4_xboole_0 @ C @ A ) @ B ) =
% 2.23/2.40         ( k4_xboole_0 @ ( k2_xboole_0 @ C @ B ) @ A ) ) ))).
% 2.23/2.40  thf('39', plain,
% 2.23/2.40      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.23/2.40         (~ (r1_xboole_0 @ X21 @ X22)
% 2.23/2.40          | ((k2_xboole_0 @ (k4_xboole_0 @ X23 @ X21) @ X22)
% 2.23/2.40              = (k4_xboole_0 @ (k2_xboole_0 @ X23 @ X22) @ X21)))),
% 2.23/2.40      inference('cnf', [status(esa)], [t87_xboole_1])).
% 2.23/2.40  thf('40', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.23/2.40         ((r2_hidden @ X0 @ X1)
% 2.23/2.40          | ((k2_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k1_tarski @ X0))
% 2.23/2.40              = (k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k1_tarski @ X0)) @ X1)))),
% 2.23/2.40      inference('sup-', [status(thm)], ['38', '39'])).
% 2.23/2.40  thf('41', plain,
% 2.23/2.40      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 2.23/2.40         (k1_tarski @ sk_B))
% 2.23/2.40         != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40             (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))),
% 2.23/2.40      inference('demod', [status(thm)], ['6', '7'])).
% 2.23/2.40  thf('42', plain,
% 2.23/2.40      ((((k2_xboole_0 @ (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)) @ 
% 2.23/2.40          (k1_tarski @ sk_A))
% 2.23/2.40          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 2.23/2.40        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 2.23/2.40      inference('sup-', [status(thm)], ['40', '41'])).
% 2.23/2.40  thf('43', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.23/2.40      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.23/2.40  thf('44', plain,
% 2.23/2.40      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40          (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B)))
% 2.23/2.40          != (k2_xboole_0 @ (k1_tarski @ sk_A) @ 
% 2.23/2.40              (k4_xboole_0 @ sk_C @ (k1_tarski @ sk_B))))
% 2.23/2.40        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 2.23/2.40      inference('demod', [status(thm)], ['42', '43'])).
% 2.23/2.40  thf('45', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 2.23/2.40      inference('simplify', [status(thm)], ['44'])).
% 2.23/2.40  thf('46', plain,
% 2.23/2.40      (![X40 : $i, X41 : $i]:
% 2.23/2.40         (((k4_xboole_0 @ X40 @ (k1_tarski @ X41)) = (X40))
% 2.23/2.40          | (r2_hidden @ X41 @ X40))),
% 2.23/2.40      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.23/2.40  thf(l33_zfmisc_1, axiom,
% 2.23/2.40    (![A:$i,B:$i]:
% 2.23/2.40     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 2.23/2.40       ( ~( r2_hidden @ A @ B ) ) ))).
% 2.23/2.40  thf('47', plain,
% 2.23/2.40      (![X30 : $i, X31 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X30 @ X31)
% 2.23/2.40          | ((k4_xboole_0 @ (k1_tarski @ X30) @ X31) != (k1_tarski @ X30)))),
% 2.23/2.40      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 2.23/2.40  thf('48', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 2.23/2.40          | (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.23/2.40          | ~ (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 2.23/2.40      inference('sup-', [status(thm)], ['46', '47'])).
% 2.23/2.40  thf('49', plain,
% 2.23/2.40      (![X0 : $i, X1 : $i]:
% 2.23/2.40         (~ (r2_hidden @ X0 @ (k1_tarski @ X1))
% 2.23/2.40          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 2.23/2.40      inference('simplify', [status(thm)], ['48'])).
% 2.23/2.40  thf('50', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 2.23/2.40      inference('sup-', [status(thm)], ['45', '49'])).
% 2.23/2.40  thf('51', plain, ($false), inference('demod', [status(thm)], ['34', '50'])).
% 2.23/2.40  
% 2.23/2.40  % SZS output end Refutation
% 2.23/2.40  
% 2.23/2.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
