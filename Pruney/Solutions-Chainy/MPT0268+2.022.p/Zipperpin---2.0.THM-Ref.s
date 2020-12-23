%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4FFpurHpbU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:55 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 103 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  569 ( 736 expanded)
%              Number of equality atoms :   62 (  81 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['31','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','45'])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('51',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4FFpurHpbU
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.19/1.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.42  % Solved by: fo/fo7.sh
% 1.19/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.42  % done 1730 iterations in 0.973s
% 1.19/1.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.42  % SZS output start Refutation
% 1.19/1.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.19/1.42  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.19/1.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.19/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.42  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.42  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.19/1.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.19/1.42  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.19/1.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.42  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.19/1.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.42  thf(t65_zfmisc_1, conjecture,
% 1.19/1.42    (![A:$i,B:$i]:
% 1.19/1.42     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.19/1.42       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.19/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.42    (~( ![A:$i,B:$i]:
% 1.19/1.42        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.19/1.42          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.19/1.42    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.19/1.42  thf('0', plain,
% 1.19/1.42      (((r2_hidden @ sk_B @ sk_A)
% 1.19/1.42        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('1', plain,
% 1.19/1.42      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.19/1.42       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.19/1.42      inference('split', [status(esa)], ['0'])).
% 1.19/1.42  thf('2', plain,
% 1.19/1.42      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.19/1.42      inference('split', [status(esa)], ['0'])).
% 1.19/1.42  thf(t69_enumset1, axiom,
% 1.19/1.42    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.19/1.42  thf('3', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 1.19/1.42      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.19/1.42  thf(t70_enumset1, axiom,
% 1.19/1.42    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.19/1.42  thf('4', plain,
% 1.19/1.42      (![X38 : $i, X39 : $i]:
% 1.19/1.42         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 1.19/1.42      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.19/1.42  thf(d1_enumset1, axiom,
% 1.19/1.42    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.42     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.19/1.42       ( ![E:$i]:
% 1.19/1.42         ( ( r2_hidden @ E @ D ) <=>
% 1.19/1.42           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.19/1.42  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.19/1.42  thf(zf_stmt_2, axiom,
% 1.19/1.42    (![E:$i,C:$i,B:$i,A:$i]:
% 1.19/1.42     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.19/1.42       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.19/1.42  thf(zf_stmt_3, axiom,
% 1.19/1.42    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.42     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.19/1.42       ( ![E:$i]:
% 1.19/1.42         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.19/1.42  thf('5', plain,
% 1.19/1.42      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.19/1.42         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 1.19/1.42          | (r2_hidden @ X30 @ X34)
% 1.19/1.42          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.19/1.42  thf('6', plain,
% 1.19/1.42      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.19/1.42         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 1.19/1.42          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 1.19/1.42      inference('simplify', [status(thm)], ['5'])).
% 1.19/1.42  thf('7', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.42         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.19/1.42          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.19/1.42      inference('sup+', [status(thm)], ['4', '6'])).
% 1.19/1.42  thf('8', plain,
% 1.19/1.42      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.42         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.19/1.42  thf('9', plain,
% 1.19/1.42      (![X25 : $i, X27 : $i, X28 : $i]:
% 1.19/1.42         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 1.19/1.42      inference('simplify', [status(thm)], ['8'])).
% 1.19/1.42  thf('10', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.19/1.42      inference('sup-', [status(thm)], ['7', '9'])).
% 1.19/1.43  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['3', '10'])).
% 1.19/1.43  thf('12', plain,
% 1.19/1.43      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.19/1.43        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.19/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.43  thf('13', plain,
% 1.19/1.43      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.19/1.43         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('split', [status(esa)], ['12'])).
% 1.19/1.43  thf(d5_xboole_0, axiom,
% 1.19/1.43    (![A:$i,B:$i,C:$i]:
% 1.19/1.43     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.19/1.43       ( ![D:$i]:
% 1.19/1.43         ( ( r2_hidden @ D @ C ) <=>
% 1.19/1.43           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.19/1.43  thf('14', plain,
% 1.19/1.43      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.19/1.43         (~ (r2_hidden @ X6 @ X5)
% 1.19/1.43          | ~ (r2_hidden @ X6 @ X4)
% 1.19/1.43          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.19/1.43      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.19/1.43  thf('15', plain,
% 1.19/1.43      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.19/1.43         (~ (r2_hidden @ X6 @ X4)
% 1.19/1.43          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.19/1.43      inference('simplify', [status(thm)], ['14'])).
% 1.19/1.43  thf('16', plain,
% 1.19/1.43      ((![X0 : $i]:
% 1.19/1.43          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.19/1.43         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['13', '15'])).
% 1.19/1.43  thf('17', plain,
% 1.19/1.43      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.19/1.43         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['11', '16'])).
% 1.19/1.43  thf('18', plain,
% 1.19/1.43      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.19/1.43       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['2', '17'])).
% 1.19/1.43  thf('19', plain,
% 1.19/1.43      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.19/1.43       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.19/1.43      inference('split', [status(esa)], ['12'])).
% 1.19/1.43  thf(l27_zfmisc_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.19/1.43  thf('20', plain,
% 1.19/1.43      (![X47 : $i, X48 : $i]:
% 1.19/1.43         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 1.19/1.43      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.19/1.43  thf(t83_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.19/1.43  thf('21', plain,
% 1.19/1.43      (![X22 : $i, X23 : $i]:
% 1.19/1.43         (((k4_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_xboole_0 @ X22 @ X23))),
% 1.19/1.43      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.19/1.43  thf('22', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((r2_hidden @ X1 @ X0)
% 1.19/1.43          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['20', '21'])).
% 1.19/1.43  thf(t48_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.19/1.43  thf('23', plain,
% 1.19/1.43      (![X16 : $i, X17 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.19/1.43           = (k3_xboole_0 @ X16 @ X17))),
% 1.19/1.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.19/1.43  thf(t36_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.19/1.43  thf('24', plain,
% 1.19/1.43      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.19/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.43  thf(l32_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.19/1.43  thf('25', plain,
% 1.19/1.43      (![X8 : $i, X10 : $i]:
% 1.19/1.43         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.19/1.43      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.19/1.43  thf('26', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['24', '25'])).
% 1.19/1.43  thf('27', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['23', '26'])).
% 1.19/1.43  thf(t49_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i,C:$i]:
% 1.19/1.43     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.19/1.43       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.19/1.43  thf('28', plain,
% 1.19/1.43      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.43         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 1.19/1.43           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 1.19/1.43      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.19/1.43  thf('29', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.19/1.43      inference('demod', [status(thm)], ['27', '28'])).
% 1.19/1.43  thf(t100_xboole_1, axiom,
% 1.19/1.43    (![A:$i,B:$i]:
% 1.19/1.43     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.19/1.43  thf('30', plain,
% 1.19/1.43      (![X11 : $i, X12 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X11 @ X12)
% 1.19/1.43           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('31', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.19/1.43           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['29', '30'])).
% 1.19/1.43  thf(t3_boole, axiom,
% 1.19/1.43    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.19/1.43  thf('32', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_boole])).
% 1.19/1.43  thf('33', plain,
% 1.19/1.43      (![X16 : $i, X17 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.19/1.43           = (k3_xboole_0 @ X16 @ X17))),
% 1.19/1.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.19/1.43  thf('34', plain,
% 1.19/1.43      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['32', '33'])).
% 1.19/1.43  thf('35', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_boole])).
% 1.19/1.43  thf('36', plain,
% 1.19/1.43      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 1.19/1.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.19/1.43  thf('37', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.19/1.43      inference('sup+', [status(thm)], ['35', '36'])).
% 1.19/1.43  thf('38', plain,
% 1.19/1.43      (![X8 : $i, X10 : $i]:
% 1.19/1.43         (((k4_xboole_0 @ X8 @ X10) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ X10))),
% 1.19/1.43      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.19/1.43  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.19/1.43      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.43  thf('40', plain,
% 1.19/1.43      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('demod', [status(thm)], ['34', '39'])).
% 1.19/1.43  thf('41', plain,
% 1.19/1.43      (![X11 : $i, X12 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X11 @ X12)
% 1.19/1.43           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.19/1.43      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.19/1.43  thf('42', plain,
% 1.19/1.43      (![X0 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['40', '41'])).
% 1.19/1.43  thf('43', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 1.19/1.43      inference('cnf', [status(esa)], [t3_boole])).
% 1.19/1.43  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.19/1.43      inference('sup+', [status(thm)], ['42', '43'])).
% 1.19/1.43  thf('45', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.19/1.43      inference('demod', [status(thm)], ['31', '44'])).
% 1.19/1.43  thf('46', plain,
% 1.19/1.43      (![X0 : $i, X1 : $i]:
% 1.19/1.43         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.19/1.43          | (r2_hidden @ X0 @ X1))),
% 1.19/1.43      inference('sup+', [status(thm)], ['22', '45'])).
% 1.19/1.43  thf('47', plain,
% 1.19/1.43      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.19/1.43         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('split', [status(esa)], ['0'])).
% 1.19/1.43  thf('48', plain,
% 1.19/1.43      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 1.19/1.43         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('sup-', [status(thm)], ['46', '47'])).
% 1.19/1.43  thf('49', plain,
% 1.19/1.43      (((r2_hidden @ sk_B @ sk_A))
% 1.19/1.43         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.19/1.43      inference('simplify', [status(thm)], ['48'])).
% 1.19/1.43  thf('50', plain,
% 1.19/1.43      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.19/1.43      inference('split', [status(esa)], ['12'])).
% 1.19/1.43  thf('51', plain,
% 1.19/1.43      (((r2_hidden @ sk_B @ sk_A)) | 
% 1.19/1.43       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.19/1.43      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.43  thf('52', plain, ($false),
% 1.19/1.43      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '51'])).
% 1.19/1.43  
% 1.19/1.43  % SZS output end Refutation
% 1.19/1.43  
% 1.19/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
