%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIXLrIlqUE

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   81 (  89 expanded)
%              Number of leaves         :   35 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  555 ( 635 expanded)
%              Number of equality atoms :   67 (  79 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X74: $i,X75: $i] :
      ( r1_tarski @ ( k1_tarski @ X74 ) @ ( k2_tarski @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','18','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','20'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('30',plain,(
    ! [X71: $i,X72: $i,X73: $i] :
      ( ( k1_enumset1 @ X71 @ X73 @ X72 )
      = ( k1_enumset1 @ X71 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_enumset1 @ sk_C @ sk_A @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['25','28','31'])).

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

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X28 )
      | ( X30 = X29 )
      | ( X30 = X26 )
      | ( X28
       != ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('37',plain,(
    ! [X26: $i,X29: $i,X30: $i] :
      ( ( X30 = X26 )
      | ( X30 = X29 )
      | ~ ( r2_hidden @ X30 @ ( k2_tarski @ X29 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_A @ sk_C )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X17 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cIXLrIlqUE
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:40:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 650 iterations in 0.226s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(t28_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.65          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.46/0.65             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t12_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X74 : $i, X75 : $i]:
% 0.46/0.65         (r1_tarski @ (k1_tarski @ X74) @ (k2_tarski @ X74 @ X75))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.46/0.65  thf(t1_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ A @ C ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X3 @ X4)
% 0.46/0.65          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.65          | (r1_tarski @ X3 @ X5))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.46/0.65          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '3'])).
% 0.46/0.65  thf(t28_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.46/0.65         = (k1_tarski @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf(t100_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.65           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.46/0.65         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(t2_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.65           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf(t5_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('12', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.65  thf(t48_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.46/0.65           = (k3_xboole_0 @ X9 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.65  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X1 @ X2)
% 0.46/0.65           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['15', '18', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.46/0.65         = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['8', '20'])).
% 0.46/0.65  thf(t98_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         ((k2_xboole_0 @ X12 @ X13)
% 0.46/0.65           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ sk_A))
% 0.46/0.65         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_boole])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ sk_A))
% 0.46/0.65         = (k2_tarski @ sk_C @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t70_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X44 : $i, X45 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 0.46/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.65  thf(t46_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.46/0.65       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.65         ((k2_enumset1 @ X39 @ X40 @ X41 @ X42)
% 0.46/0.65           = (k2_xboole_0 @ (k1_enumset1 @ X39 @ X40 @ X41) @ (k1_tarski @ X42)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.46/0.65           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf(t71_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.46/0.65         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 0.46/0.65           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 0.46/0.65      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.46/0.65  thf(t98_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X71 : $i, X72 : $i, X73 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X71 @ X73 @ X72) = (k1_enumset1 @ X71 @ X72 @ X73))),
% 0.46/0.65      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (((k1_enumset1 @ sk_C @ sk_A @ sk_D_1) = (k2_tarski @ sk_C @ sk_D_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '28', '31'])).
% 0.46/0.65  thf(d1_enumset1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.65       ( ![E:$i]:
% 0.46/0.65         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.65           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_2, axiom,
% 0.46/0.65    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.65       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_3, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.65       ( ![E:$i]:
% 0.46/0.65         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.46/0.65          | (r2_hidden @ X19 @ X23)
% 0.46/0.65          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.65         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.46/0.65          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.46/0.65      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D_1))
% 0.46/0.65          | (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_A @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['32', '34'])).
% 0.46/0.65  thf(d2_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X26 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X30 @ X28)
% 0.46/0.65          | ((X30) = (X29))
% 0.46/0.65          | ((X30) = (X26))
% 0.46/0.65          | ((X28) != (k2_tarski @ X29 @ X26)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d2_tarski])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X26 : $i, X29 : $i, X30 : $i]:
% 0.46/0.65         (((X30) = (X26))
% 0.46/0.65          | ((X30) = (X29))
% 0.46/0.65          | ~ (r2_hidden @ X30 @ (k2_tarski @ X29 @ X26)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ X0 @ sk_D_1 @ sk_A @ sk_C)
% 0.46/0.65          | ((X0) = (sk_C))
% 0.46/0.65          | ((X0) = (sk_D_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         (((X15) != (X17)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.46/0.65         ~ (zip_tseitin_0 @ X17 @ X16 @ X17 @ X14)),
% 0.46/0.65      inference('simplify', [status(thm)], ['39'])).
% 0.46/0.65  thf('41', plain, ((((sk_A) = (sk_D_1)) | ((sk_A) = (sk_C)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['38', '40'])).
% 0.46/0.65  thf('42', plain, (((sk_A) != (sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('43', plain, (((sk_A) != (sk_D_1))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['41', '42', '43'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
