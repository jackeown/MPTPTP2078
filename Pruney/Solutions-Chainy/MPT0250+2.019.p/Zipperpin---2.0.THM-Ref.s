%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7UlxCkp8tB

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:49 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 114 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  527 ( 813 expanded)
%              Number of equality atoms :   37 (  60 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','23'])).

thf('25',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X43 ) @ X44 )
      | ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('26',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ X14 @ ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('36',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','33','34','35'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sup-',[status(thm)],['24','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7UlxCkp8tB
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 281 iterations in 0.136s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.39/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.39/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.59  thf(t70_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X34 : $i, X35 : $i]:
% 0.39/0.59         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.39/0.59  thf(d1_enumset1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.59       ( ![E:$i]:
% 0.39/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.39/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.39/0.59  thf(zf_stmt_1, axiom,
% 0.39/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.39/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.39/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.39/0.59       ( ![E:$i]:
% 0.39/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.59         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.39/0.59          | (r2_hidden @ X26 @ X30)
% 0.39/0.59          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.59         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 0.39/0.59          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 0.39/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.39/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['0', '2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.59         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.39/0.59         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 0.39/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.39/0.59      inference('sup-', [status(thm)], ['3', '5'])).
% 0.39/0.59  thf(t69_enumset1, axiom,
% 0.39/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.59  thf('7', plain, (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.39/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.59  thf(l27_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X43 : $i, X44 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ (k1_tarski @ X43) @ X44) | (r2_hidden @ X43 @ X44))),
% 0.39/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.39/0.59  thf(t83_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_hidden @ X1 @ X0)
% 0.39/0.59          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.39/0.59  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.39/0.59  thf(t100_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i]:
% 0.39/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.39/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.59  thf(t1_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.39/0.59       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         ((r2_hidden @ X1 @ X2)
% 0.39/0.59          | (r2_hidden @ X1 @ X3)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X2 @ X3)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.39/0.59          | (r2_hidden @ X1 @ X0)
% 0.39/0.59          | (r2_hidden @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['15'])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ X2)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ X3)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X2 @ X3)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.39/0.59          | ~ (r2_hidden @ X1 @ X0)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ X0)
% 0.39/0.59          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['19'])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('clc', [status(thm)], ['16', '20'])).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.39/0.59          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['10', '21'])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.39/0.59          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '22'])).
% 0.39/0.59  thf('24', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['6', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X43 : $i, X44 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ (k1_tarski @ X43) @ X44) | (r2_hidden @ X43 @ X44))),
% 0.39/0.59      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.39/0.59  thf(t45_zfmisc_1, conjecture,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.39/0.59       ( r2_hidden @ A @ B ) ))).
% 0.39/0.59  thf(zf_stmt_3, negated_conjecture,
% 0.39/0.59    (~( ![A:$i,B:$i]:
% 0.39/0.59        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.39/0.59          ( r2_hidden @ A @ B ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf(d10_xboole_0, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (![X5 : $i, X7 : $i]:
% 0.39/0.59         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.39/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.39/0.59        | ((sk_B) = (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf(commutativity_k2_tarski, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.59  thf(l51_zfmisc_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (![X45 : $i, X46 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (![X45 : $i, X46 : $i]:
% 0.39/0.59         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 0.39/0.59      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.59  thf(t7_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i]: (r1_tarski @ X14 @ (k2_xboole_0 @ X14 @ X15))),
% 0.39/0.59      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.39/0.59  thf('36', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['28', '33', '34', '35'])).
% 0.39/0.59  thf(t70_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.39/0.59       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.39/0.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.39/0.59         ((r1_xboole_0 @ X10 @ X13)
% 0.39/0.59          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r1_xboole_0 @ X0 @ sk_B) | (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ sk_B)
% 0.39/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (![X16 : $i, X17 : $i]:
% 0.39/0.59         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ sk_B)
% 0.39/0.59          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A))
% 0.39/0.59              = (k1_tarski @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.39/0.59      inference('clc', [status(thm)], ['16', '20'])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf('44', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.39/0.59  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.39/0.59      inference('clc', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf('46', plain, ($false), inference('sup-', [status(thm)], ['24', '45'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
