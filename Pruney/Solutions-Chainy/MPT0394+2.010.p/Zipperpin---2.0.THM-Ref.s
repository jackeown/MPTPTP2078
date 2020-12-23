%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gKr0uriQzU

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 135 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  604 ( 987 expanded)
%              Number of equality atoms :   71 ( 110 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k2_enumset1 @ X39 @ X39 @ X40 @ X41 )
      = ( k1_enumset1 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X27 @ X28 @ X29 @ X30 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X27 @ X28 @ X29 ) @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('19',plain,(
    ! [X48: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X46 @ X47 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X46 ) @ ( k1_setfam_1 @ X47 ) ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X48: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('43',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','46'])).

thf('48',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ~ ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gKr0uriQzU
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:16:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 537 iterations in 0.329s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.53/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.75  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.53/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.75  thf(t71_enumset1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.53/0.75         ((k2_enumset1 @ X39 @ X39 @ X40 @ X41)
% 0.53/0.75           = (k1_enumset1 @ X39 @ X40 @ X41))),
% 0.53/0.75      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.53/0.75  thf(t70_enumset1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.75  thf('1', plain,
% 0.53/0.75      (![X37 : $i, X38 : $i]:
% 0.53/0.75         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.53/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X37 : $i, X38 : $i]:
% 0.53/0.75         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.53/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.75  thf(d1_enumset1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.75       ( ![E:$i]:
% 0.53/0.75         ( ( r2_hidden @ E @ D ) <=>
% 0.53/0.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.53/0.75  thf(zf_stmt_1, axiom,
% 0.53/0.75    (![E:$i,C:$i,B:$i,A:$i]:
% 0.53/0.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.53/0.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_2, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.75       ( ![E:$i]:
% 0.53/0.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.75         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.53/0.75          | (r2_hidden @ X20 @ X24)
% 0.53/0.75          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.75         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.53/0.75          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.53/0.75      inference('simplify', [status(thm)], ['4'])).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.53/0.75          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['3', '5'])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.75         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.53/0.75         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.53/0.75      inference('simplify', [status(thm)], ['7'])).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['6', '8'])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r2_hidden @ X1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['2', '9'])).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (r2_hidden @ X1 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['2', '9'])).
% 0.53/0.75  thf(t69_enumset1, axiom,
% 0.53/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.53/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X37 : $i, X38 : $i]:
% 0.53/0.75         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.53/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.75  thf(t46_enumset1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.75     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.53/0.75       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.75         ((k2_enumset1 @ X27 @ X28 @ X29 @ X30)
% 0.53/0.75           = (k2_xboole_0 @ (k1_enumset1 @ X27 @ X28 @ X29) @ (k1_tarski @ X30)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.53/0.75           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['0', '1'])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.53/0.75           = (k2_tarski @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['15', '16'])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.53/0.75           = (k2_tarski @ X0 @ X1))),
% 0.53/0.75      inference('sup+', [status(thm)], ['12', '17'])).
% 0.53/0.75  thf(t11_setfam_1, axiom,
% 0.53/0.75    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.53/0.75  thf('19', plain, (![X48 : $i]: ((k1_setfam_1 @ (k1_tarski @ X48)) = (X48))),
% 0.53/0.75      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.53/0.75  thf(t10_setfam_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.75          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.53/0.75            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      (![X46 : $i, X47 : $i]:
% 0.53/0.75         (((X46) = (k1_xboole_0))
% 0.53/0.75          | ((k1_setfam_1 @ (k2_xboole_0 @ X46 @ X47))
% 0.53/0.75              = (k3_xboole_0 @ (k1_setfam_1 @ X46) @ (k1_setfam_1 @ X47)))
% 0.53/0.75          | ((X47) = (k1_xboole_0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.53/0.75            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.53/0.75          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.53/0.75          | ((X1) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['19', '20'])).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.53/0.75            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.53/0.75          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.53/0.75          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['18', '21'])).
% 0.53/0.75  thf('23', plain, (![X48 : $i]: ((k1_setfam_1 @ (k1_tarski @ X48)) = (X48))),
% 0.53/0.75      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.53/0.75          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.53/0.75          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['22', '23'])).
% 0.53/0.75  thf(t12_setfam_1, conjecture,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf(zf_stmt_3, negated_conjecture,
% 0.53/0.75    (~( ![A:$i,B:$i]:
% 0.53/0.75        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.53/0.75         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.53/0.75        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.53/0.75        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.75        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['26'])).
% 0.53/0.75  thf(l24_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X42 : $i, X43 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ (k1_tarski @ X42) @ X43) | ~ (r2_hidden @ X42 @ X43))),
% 0.53/0.75      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.53/0.75  thf('29', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.75          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.75          | ~ (r2_hidden @ sk_B @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf(t17_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.75  thf('30', plain,
% 0.53/0.75      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.53/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.75  thf(t2_boole, axiom,
% 0.53/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.53/0.75      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.75  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.75      inference('sup+', [status(thm)], ['31', '32'])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('34', plain,
% 0.53/0.75      (![X2 : $i, X4 : $i]:
% 0.53/0.75         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.75  thf('36', plain,
% 0.53/0.75      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['30', '35'])).
% 0.53/0.75  thf(t48_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.53/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X10 : $i, X11 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.53/0.75           = (k3_xboole_0 @ X10 @ X11))),
% 0.53/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.75           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['37', '38'])).
% 0.53/0.75  thf(t47_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.75  thf('40', plain,
% 0.53/0.75      (![X8 : $i, X9 : $i]:
% 0.53/0.75         ((k4_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9))
% 0.53/0.75           = (k4_xboole_0 @ X8 @ X9))),
% 0.53/0.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.53/0.75           = (k4_xboole_0 @ X1 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['39', '40'])).
% 0.53/0.75  thf('42', plain,
% 0.53/0.75      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['36', '41'])).
% 0.53/0.75  thf(t83_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.75  thf('43', plain,
% 0.53/0.75      (![X12 : $i, X14 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.53/0.75  thf('44', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.53/0.75  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.75  thf('46', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['29', '45'])).
% 0.53/0.75  thf('47', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['11', '46'])).
% 0.53/0.75  thf('48', plain,
% 0.53/0.75      (![X42 : $i, X43 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ (k1_tarski @ X42) @ X43) | ~ (r2_hidden @ X42 @ X43))),
% 0.53/0.75      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.75  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.75  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.53/0.75      inference('demod', [status(thm)], ['49', '50'])).
% 0.53/0.75  thf('52', plain, ($false), inference('sup-', [status(thm)], ['10', '51'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
