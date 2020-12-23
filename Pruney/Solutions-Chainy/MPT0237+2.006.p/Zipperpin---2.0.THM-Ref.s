%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QplSAR2rO9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:59 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 185 expanded)
%              Number of leaves         :   30 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  589 (1444 expanded)
%              Number of equality atoms :   68 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X57: $i,X58: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X57 ) @ ( k1_tarski @ X58 ) )
        = ( k2_tarski @ X57 @ X58 ) )
      | ( X57 = X58 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

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

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X26 != X25 )
      | ( r2_hidden @ X26 @ X27 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X25: $i] :
      ( r2_hidden @ X25 @ ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X17: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X17 @ X19 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('39',plain,(
    ! [X59: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X59 ) )
      = X59 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['3','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('50',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('53',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['50'])).

thf('54',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','51','52','53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QplSAR2rO9
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:54:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 675 iterations in 0.233s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.69  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.69  thf(t32_zfmisc_1, conjecture,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.45/0.69       ( k2_tarski @ A @ B ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i]:
% 0.45/0.69        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.45/0.69          ( k2_tarski @ A @ B ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.45/0.69         != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(l51_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X53 : $i, X54 : $i]:
% 0.45/0.69         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.45/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.69         != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf(t29_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( A ) != ( B ) ) =>
% 0.45/0.69       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.69         ( k2_tarski @ A @ B ) ) ))).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X57 : $i, X58 : $i]:
% 0.45/0.69         (((k5_xboole_0 @ (k1_tarski @ X57) @ (k1_tarski @ X58))
% 0.45/0.69            = (k2_tarski @ X57 @ X58))
% 0.45/0.69          | ((X57) = (X58)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.45/0.69  thf(t3_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf(d1_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X28 @ X27)
% 0.45/0.69          | ((X28) = (X25))
% 0.45/0.69          | ((X27) != (k1_tarski @ X25)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X25 : $i, X28 : $i]:
% 0.45/0.69         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.45/0.69          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '6'])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X6 : $i, X7 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      (![X25 : $i, X28 : $i]:
% 0.45/0.69         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.45/0.69          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((X0) = (X1))
% 0.45/0.69          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.45/0.69          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['7', '10'])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) | ((X0) = (X1)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.69  thf(d3_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X3 : $i, X5 : $i]:
% 0.45/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf(t4_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.45/0.69          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.45/0.69          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (((X1) = (X0))
% 0.45/0.69          | (r1_tarski @ (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 0.45/0.69             X2))),
% 0.45/0.69      inference('sup-', [status(thm)], ['12', '15'])).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X3 : $i, X5 : $i]:
% 0.45/0.69         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.69  thf('18', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.69         (((X26) != (X25))
% 0.45/0.69          | (r2_hidden @ X26 @ X27)
% 0.45/0.69          | ((X27) != (k1_tarski @ X25)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.69  thf('20', plain, (![X25 : $i]: (r2_hidden @ X25 @ (k1_tarski @ X25))),
% 0.45/0.69      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X8 @ X6)
% 0.45/0.69          | ~ (r2_hidden @ X8 @ X9)
% 0.45/0.69          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['18', '22'])).
% 0.45/0.69  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['17', '23'])).
% 0.45/0.69  thf(d10_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X14 : $i, X16 : $i]:
% 0.45/0.69         (((X14) = (X16))
% 0.45/0.69          | ~ (r1_tarski @ X16 @ X14)
% 0.45/0.69          | ~ (r1_tarski @ X14 @ X16))),
% 0.45/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((X1) = (X0))
% 0.45/0.69          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.45/0.69              = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['16', '26'])).
% 0.45/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.69  thf(t100_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X20 : $i, X21 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X20 @ X21)
% 0.45/0.69           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.45/0.69            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 0.45/0.69          | ((X1) = (X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.69  thf('33', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.45/0.69      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.69  thf(l32_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X17 : $i, X19 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ X17 @ X19) = (k1_xboole_0))
% 0.45/0.69          | ~ (r1_tarski @ X17 @ X19))),
% 0.45/0.69      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.45/0.69  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf(t98_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X23 : $i, X24 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.45/0.69           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf(t69_enumset1, axiom,
% 0.45/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.45/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.69  thf(t31_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.69  thf('39', plain, (![X59 : $i]: ((k3_tarski @ (k1_tarski @ X59)) = (X59))),
% 0.45/0.69      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.45/0.69  thf('40', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['38', '39'])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      (![X53 : $i, X54 : $i]:
% 0.45/0.69         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.45/0.69      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.45/0.69  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.45/0.69  thf('43', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['37', '42'])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.45/0.69            = (k1_tarski @ X0))
% 0.45/0.69          | ((X1) = (X0)))),
% 0.45/0.69      inference('demod', [status(thm)], ['31', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X23 : $i, X24 : $i]:
% 0.45/0.69         ((k2_xboole_0 @ X23 @ X24)
% 0.45/0.69           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.45/0.69            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.45/0.69          | ((X1) = (X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.45/0.69            = (k2_tarski @ X1 @ X0))
% 0.45/0.69          | ((X1) = (X0))
% 0.45/0.69          | ((X1) = (X0)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['3', '46'])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (((X1) = (X0))
% 0.45/0.69          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.45/0.69              = (k2_tarski @ X1 @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.69         != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.53/0.69        | ((sk_A) = (sk_B)))),
% 0.53/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.69  thf('51', plain, (((sk_A) = (sk_B))),
% 0.53/0.69      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.69  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.53/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.53/0.69  thf('53', plain, (((sk_A) = (sk_B))),
% 0.53/0.69      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.69  thf('54', plain,
% 0.53/0.69      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.53/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.69  thf('55', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.53/0.69      inference('demod', [status(thm)], ['2', '51', '52', '53', '54'])).
% 0.53/0.69  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.53/0.69  
% 0.53/0.69  % SZS output end Refutation
% 0.53/0.69  
% 0.53/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
