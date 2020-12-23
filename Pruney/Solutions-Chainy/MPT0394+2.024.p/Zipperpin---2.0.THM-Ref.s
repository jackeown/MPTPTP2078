%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sr5EBLZAyp

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 347 expanded)
%              Number of leaves         :   30 ( 120 expanded)
%              Depth                    :   14
%              Number of atoms          :  589 (2829 expanded)
%              Number of equality atoms :   81 ( 362 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k2_enumset1 @ X26 @ X26 @ X27 @ X28 )
      = ( k1_enumset1 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X19 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X19 @ X20 @ X21 ) @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('10',plain,(
    ! [X35: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X33 @ X34 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X33 ) @ ( k1_setfam_1 @ X34 ) ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X35: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('25',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X35: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('34',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('36',plain,(
    ! [X35: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X35 ) )
      = X35 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('37',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('41',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['28','31'])).

thf('45',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['32','33'])).

thf('46',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['34','41'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','54','55'])).

thf('57',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','42','43','44','45','46','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sr5EBLZAyp
% 0.14/0.37  % Computer   : n016.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 10:20:34 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 307 iterations in 0.179s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(t12_setfam_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i]:
% 0.45/0.66        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.66         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t71_enumset1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.66         ((k2_enumset1 @ X26 @ X26 @ X27 @ X28)
% 0.45/0.66           = (k1_enumset1 @ X26 @ X27 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.66  thf(t70_enumset1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i]:
% 0.45/0.66         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i]:
% 0.45/0.66         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.66  thf(t46_enumset1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.45/0.66       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.45/0.66         ((k2_enumset1 @ X19 @ X20 @ X21 @ X22)
% 0.45/0.66           = (k2_xboole_0 @ (k1_enumset1 @ X19 @ X20 @ X21) @ (k1_tarski @ X22)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.66           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_tarski @ X1 @ X0)
% 0.45/0.66           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['3', '6'])).
% 0.45/0.66  thf(t69_enumset1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.66  thf('8', plain, (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k2_tarski @ X1 @ X0)
% 0.45/0.66           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf(t11_setfam_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.66  thf('10', plain, (![X35 : $i]: ((k1_setfam_1 @ (k1_tarski @ X35)) = (X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.66  thf(t10_setfam_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.45/0.66            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i]:
% 0.45/0.66         (((X33) = (k1_xboole_0))
% 0.45/0.66          | ((k1_setfam_1 @ (k2_xboole_0 @ X33 @ X34))
% 0.45/0.66              = (k3_xboole_0 @ (k1_setfam_1 @ X33) @ (k1_setfam_1 @ X34)))
% 0.45/0.66          | ((X34) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.66            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.45/0.66          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.45/0.66          | ((X1) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.45/0.66            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.45/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['9', '12'])).
% 0.45/0.66  thf('14', plain, (![X35 : $i]: ((k1_setfam_1 @ (k1_tarski @ X35)) = (X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.66         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.45/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i]:
% 0.45/0.66         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.66  thf(d1_enumset1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.66       ( ![E:$i]:
% 0.45/0.66         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.66           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_2, axiom,
% 0.45/0.66    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.66     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.66       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_3, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.66       ( ![E:$i]:
% 0.45/0.66         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.45/0.66          | (r2_hidden @ X12 @ X16)
% 0.45/0.66          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.66         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.45/0.66          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.45/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.66          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['20', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.45/0.66      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '25'])).
% 0.45/0.66  thf('27', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['19', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['18', '27'])).
% 0.45/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.66  thf('29', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.66  thf(l24_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ X30) | ~ (r2_hidden @ X29 @ X30))),
% 0.45/0.66      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.45/0.66  thf('31', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('32', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.66      inference('clc', [status(thm)], ['28', '31'])).
% 0.45/0.66  thf('33', plain, (![X35 : $i]: ((k1_setfam_1 @ (k1_tarski @ X35)) = (X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.66  thf('34', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.66        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.66  thf('36', plain, (![X35 : $i]: ((k1_setfam_1 @ (k1_tarski @ X35)) = (X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.66        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['19', '26'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.45/0.66        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.66  thf('41', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.45/0.66      inference('clc', [status(thm)], ['39', '40'])).
% 0.45/0.66  thf('42', plain, (((sk_A) = (sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['34', '41'])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.66      inference('clc', [status(thm)], ['28', '31'])).
% 0.45/0.66  thf('45', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['32', '33'])).
% 0.45/0.66  thf('46', plain, (((sk_A) = (sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['34', '41'])).
% 0.45/0.66  thf(t2_boole, axiom,
% 0.45/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X1 : $i, X2 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.45/0.66           = (k3_xboole_0 @ X1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X1 : $i, X2 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X2))
% 0.45/0.66           = (k3_xboole_0 @ X1 @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.45/0.66           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.45/0.66           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['47', '50'])).
% 0.45/0.66  thf('52', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.66  thf(t83_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         (((k4_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.45/0.66  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('56', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '54', '55'])).
% 0.45/0.66  thf('57', plain, (((sk_A) != (sk_A))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['0', '42', '43', '44', '45', '46', '56'])).
% 0.45/0.66  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
