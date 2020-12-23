%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3f1Gn37AF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:21 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   83 (  92 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  598 ( 684 expanded)
%              Number of equality atoms :   75 (  88 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','14','15'])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','16'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('31',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X65 @ X67 @ X66 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf(t102_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ C @ B @ A ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X31 @ X30 @ X29 )
      = ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t102_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['21','30','33'])).

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

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X25 )
      | ( X27 = X26 )
      | ( X27 = X23 )
      | ( X25
       != ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('39',plain,(
    ! [X23: $i,X26: $i,X27: $i] :
      ( ( X27 = X23 )
      | ( X27 = X26 )
      | ~ ( r2_hidden @ X27 @ ( k2_tarski @ X26 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_B )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('42',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A3f1Gn37AF
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:03:26 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 807 iterations in 0.310s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.55/0.78  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.55/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.78  thf(t25_zfmisc_1, conjecture,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.55/0.78          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.78        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.55/0.78             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.55/0.78  thf('0', plain,
% 0.55/0.78      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t28_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.78  thf('1', plain,
% 0.55/0.78      (![X3 : $i, X4 : $i]:
% 0.55/0.78         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.55/0.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.55/0.78         = (k1_tarski @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.78  thf(t100_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.78  thf('3', plain,
% 0.55/0.78      (![X1 : $i, X2 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.55/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.55/0.78         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['2', '3'])).
% 0.55/0.78  thf(t2_boole, axiom,
% 0.55/0.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.78  thf('6', plain,
% 0.55/0.78      (![X1 : $i, X2 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.55/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.78  thf('7', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['5', '6'])).
% 0.55/0.78  thf(t5_boole, axiom,
% 0.55/0.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.78  thf('8', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.78  thf('9', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.78      inference('demod', [status(thm)], ['7', '8'])).
% 0.55/0.78  thf(t48_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (![X6 : $i, X7 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.55/0.78           = (k3_xboole_0 @ X6 @ X7))),
% 0.55/0.78      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['9', '10'])).
% 0.55/0.78  thf(idempotence_k3_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.55/0.78  thf('12', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (![X1 : $i, X2 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X1 @ X2)
% 0.55/0.78           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.78  thf('14', plain,
% 0.55/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['12', '13'])).
% 0.55/0.78  thf('15', plain,
% 0.55/0.78      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.78  thf('16', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '14', '15'])).
% 0.55/0.78  thf('17', plain,
% 0.55/0.78      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.55/0.78         = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['4', '16'])).
% 0.55/0.78  thf(t98_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.78  thf('18', plain,
% 0.55/0.78      (![X9 : $i, X10 : $i]:
% 0.55/0.78         ((k2_xboole_0 @ X9 @ X10)
% 0.55/0.78           = (k5_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.78  thf('19', plain,
% 0.55/0.78      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.55/0.78         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['17', '18'])).
% 0.55/0.78  thf('20', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.78  thf('21', plain,
% 0.55/0.78      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.55/0.78         = (k2_tarski @ sk_B @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['19', '20'])).
% 0.55/0.78  thf(t72_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.78     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.55/0.78  thf('22', plain,
% 0.55/0.78      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.55/0.78         ((k3_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46)
% 0.55/0.78           = (k2_enumset1 @ X43 @ X44 @ X45 @ X46))),
% 0.55/0.78      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.55/0.78  thf(t71_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.78  thf('23', plain,
% 0.55/0.78      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.55/0.78         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 0.55/0.78           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 0.55/0.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.78  thf('24', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['22', '23'])).
% 0.55/0.78  thf('25', plain,
% 0.55/0.78      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.55/0.78         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 0.55/0.78           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 0.55/0.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.78  thf(t50_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.55/0.78     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.55/0.78       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.55/0.78  thf('26', plain,
% 0.55/0.78      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.55/0.78         ((k3_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.55/0.78           = (k2_xboole_0 @ (k2_enumset1 @ X32 @ X33 @ X34 @ X35) @ 
% 0.55/0.78              (k1_tarski @ X36)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.55/0.78  thf('27', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.78         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.55/0.78           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['25', '26'])).
% 0.55/0.78  thf('28', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.55/0.78           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.78      inference('sup+', [status(thm)], ['24', '27'])).
% 0.55/0.78  thf(t70_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.78  thf('29', plain,
% 0.55/0.78      (![X38 : $i, X39 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.55/0.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.78  thf('30', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.55/0.78           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.78      inference('demod', [status(thm)], ['28', '29'])).
% 0.55/0.78  thf(t98_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.55/0.78  thf('31', plain,
% 0.55/0.78      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X65 @ X67 @ X66) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.55/0.78      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.55/0.78  thf(t102_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ C @ B @ A ) ))).
% 0.55/0.78  thf('32', plain,
% 0.55/0.78      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X31 @ X30 @ X29) = (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.55/0.78      inference('cnf', [status(esa)], [t102_enumset1])).
% 0.55/0.78  thf('33', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.78         ((k1_enumset1 @ X1 @ X0 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['31', '32'])).
% 0.55/0.78  thf('34', plain,
% 0.55/0.78      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.55/0.78      inference('demod', [status(thm)], ['21', '30', '33'])).
% 0.55/0.78  thf(d1_enumset1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.78     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.78       ( ![E:$i]:
% 0.55/0.78         ( ( r2_hidden @ E @ D ) <=>
% 0.55/0.78           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.55/0.78  thf(zf_stmt_2, axiom,
% 0.55/0.78    (![E:$i,C:$i,B:$i,A:$i]:
% 0.55/0.78     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.55/0.78       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_3, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.78     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.78       ( ![E:$i]:
% 0.55/0.78         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.55/0.78  thf('35', plain,
% 0.55/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.55/0.78         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.55/0.78          | (r2_hidden @ X16 @ X20)
% 0.55/0.78          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.78  thf('36', plain,
% 0.55/0.78      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.78         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.55/0.78          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.55/0.78      inference('simplify', [status(thm)], ['35'])).
% 0.55/0.78  thf('37', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.55/0.78          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.55/0.78      inference('sup+', [status(thm)], ['34', '36'])).
% 0.55/0.78  thf(d2_tarski, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.55/0.78       ( ![D:$i]:
% 0.55/0.78         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.55/0.78  thf('38', plain,
% 0.55/0.78      (![X23 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X27 @ X25)
% 0.55/0.78          | ((X27) = (X26))
% 0.55/0.78          | ((X27) = (X23))
% 0.55/0.78          | ((X25) != (k2_tarski @ X26 @ X23)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d2_tarski])).
% 0.55/0.78  thf('39', plain,
% 0.55/0.78      (![X23 : $i, X26 : $i, X27 : $i]:
% 0.55/0.78         (((X27) = (X23))
% 0.55/0.78          | ((X27) = (X26))
% 0.55/0.78          | ~ (r2_hidden @ X27 @ (k2_tarski @ X26 @ X23)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['38'])).
% 0.55/0.78  thf('40', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.55/0.78          | ((X0) = (sk_B))
% 0.55/0.78          | ((X0) = (sk_C)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['37', '39'])).
% 0.55/0.78  thf('41', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.78         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.78  thf('42', plain,
% 0.55/0.78      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.55/0.78         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.55/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.55/0.78  thf('43', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_B)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['40', '42'])).
% 0.55/0.78  thf('44', plain, (((sk_A) != (sk_B))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('45', plain, (((sk_A) != (sk_C))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('46', plain, ($false),
% 0.55/0.78      inference('simplify_reflect-', [status(thm)], ['43', '44', '45'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
