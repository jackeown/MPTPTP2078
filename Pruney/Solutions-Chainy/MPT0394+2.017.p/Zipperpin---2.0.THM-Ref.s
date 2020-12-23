%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnbQiVbqF8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 460 expanded)
%              Number of leaves         :   25 ( 150 expanded)
%              Depth                    :   14
%              Number of atoms          :  533 (3956 expanded)
%              Number of equality atoms :   78 ( 573 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X16 @ X17 @ X18 )
      = ( k2_xboole_0 @ ( k2_tarski @ X16 @ X17 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('6',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X29 ) @ ( k1_setfam_1 @ X30 ) ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
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

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('25',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('35',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('37',plain,(
    ! [X31: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('38',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','22'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('42',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(clc,[status(thm)],['40','45'])).

thf('47',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['35','46'])).

thf('48',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','32'])).

thf('50',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['33','34'])).

thf('51',plain,(
    sk_A = sk_B ),
    inference('sup+',[status(thm)],['35','46'])).

thf('52',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('53',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','47','48','49','50','51','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CnbQiVbqF8
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 118 iterations in 0.054s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.19/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.19/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(t12_setfam_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.19/0.50         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('1', plain, (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(t43_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.19/0.50       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X16 @ X17 @ X18)
% 0.19/0.50           = (k2_xboole_0 @ (k2_tarski @ X16 @ X17) @ (k1_tarski @ X18)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.19/0.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf(t70_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((k2_tarski @ X0 @ X1)
% 0.19/0.50           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf(t11_setfam_1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.19/0.50  thf('6', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.19/0.50  thf(t10_setfam_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.19/0.50            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X29 : $i, X30 : $i]:
% 0.19/0.50         (((X29) = (k1_xboole_0))
% 0.19/0.50          | ((k1_setfam_1 @ (k2_xboole_0 @ X29 @ X30))
% 0.19/0.50              = (k3_xboole_0 @ (k1_setfam_1 @ X29) @ (k1_setfam_1 @ X30)))
% 0.19/0.50          | ((X30) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.19/0.50            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.19/0.50          | ((X1) = (k1_xboole_0))
% 0.19/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.19/0.50          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.19/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['5', '8'])).
% 0.19/0.50  thf('10', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.19/0.50          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.19/0.50          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.19/0.50         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.19/0.50        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.19/0.50        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X20 : $i, X21 : $i]:
% 0.19/0.50         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.19/0.50  thf(d1_enumset1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.19/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.19/0.50  thf(zf_stmt_2, axiom,
% 0.19/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.19/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.19/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_3, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.19/0.50       ( ![E:$i]:
% 0.19/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.19/0.50          | (r2_hidden @ X9 @ X13)
% 0.19/0.50          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.50         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.19/0.50          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.19/0.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['16', '18'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.19/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '21'])).
% 0.19/0.50  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['15', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['14', '23'])).
% 0.19/0.50  thf(idempotence_k3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.19/0.50  thf('25', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.50  thf(d7_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.19/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.50  thf(l24_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X25) @ X26) | ~ (r2_hidden @ X25 @ X26))),
% 0.19/0.50      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.50          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ sk_B @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_B @ k1_xboole_0)
% 0.19/0.50        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['28', '31'])).
% 0.19/0.50  thf('33', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('clc', [status(thm)], ['24', '32'])).
% 0.19/0.50  thf('34', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.19/0.50  thf('35', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.19/0.50        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.50  thf('37', plain, (![X31 : $i]: ((k1_setfam_1 @ (k1_tarski @ X31)) = (X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.19/0.50        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['15', '22'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ k1_xboole_0)
% 0.19/0.50        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.50  thf('41', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.19/0.50        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ (k1_tarski @ X25) @ X26) | ~ (r2_hidden @ X25 @ X26))),
% 0.19/0.50      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.19/0.50          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.19/0.50          | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      ((~ (r2_hidden @ sk_A @ k1_xboole_0)
% 0.19/0.50        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['41', '44'])).
% 0.19/0.50  thf('46', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.19/0.50      inference('clc', [status(thm)], ['40', '45'])).
% 0.19/0.50  thf('47', plain, (((sk_A) = (sk_B))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf('49', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.19/0.50      inference('clc', [status(thm)], ['24', '32'])).
% 0.19/0.50  thf('50', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('51', plain, (((sk_A) = (sk_B))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '46'])).
% 0.19/0.50  thf('52', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.19/0.50  thf('53', plain, (((sk_A) != (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)],
% 0.19/0.50                ['0', '47', '48', '49', '50', '51', '52'])).
% 0.19/0.50  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
