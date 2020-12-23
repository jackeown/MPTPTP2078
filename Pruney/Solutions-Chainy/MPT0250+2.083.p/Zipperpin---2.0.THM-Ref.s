%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ym6bauURxb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:58 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 120 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :   22
%              Number of atoms          :  587 ( 996 expanded)
%              Number of equality atoms :   37 (  73 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
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

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('44',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( r2_hidden @ X52 @ X50 )
      | ( r2_hidden @ X52 @ X53 )
      | ( X53
       != ( k3_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('45',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( r2_hidden @ X52 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X52 @ X50 )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('48',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ym6bauURxb
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 1083 iterations in 0.760s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.21  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.02/1.21  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.02/1.21  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.02/1.21  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.02/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.21  thf(t45_zfmisc_1, conjecture,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.02/1.21       ( r2_hidden @ A @ B ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i,B:$i]:
% 1.02/1.21        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.02/1.21          ( r2_hidden @ A @ B ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 1.02/1.21  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t70_enumset1, axiom,
% 1.02/1.21    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.02/1.21  thf('1', plain,
% 1.02/1.21      (![X17 : $i, X18 : $i]:
% 1.02/1.21         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.02/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.21  thf(d1_enumset1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.21       ( ![E:$i]:
% 1.02/1.21         ( ( r2_hidden @ E @ D ) <=>
% 1.02/1.21           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.02/1.21  thf(zf_stmt_2, axiom,
% 1.02/1.21    (![E:$i,C:$i,B:$i,A:$i]:
% 1.02/1.21     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.02/1.21       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_3, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.21     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.21       ( ![E:$i]:
% 1.02/1.21         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.02/1.21  thf('2', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.02/1.21         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.02/1.21          | (r2_hidden @ X9 @ X13)
% 1.02/1.21          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.21  thf('3', plain,
% 1.02/1.21      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.02/1.21         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 1.02/1.21          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 1.02/1.21      inference('simplify', [status(thm)], ['2'])).
% 1.02/1.21  thf('4', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.21          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.21      inference('sup+', [status(thm)], ['1', '3'])).
% 1.02/1.21  thf('5', plain,
% 1.02/1.21      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.02/1.21         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.21  thf('6', plain,
% 1.02/1.21      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 1.02/1.21      inference('simplify', [status(thm)], ['5'])).
% 1.02/1.21  thf('7', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '6'])).
% 1.02/1.21  thf('8', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '6'])).
% 1.02/1.21  thf(t71_enumset1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.21         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.02/1.21           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.02/1.21      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.02/1.21  thf('10', plain,
% 1.02/1.21      (![X17 : $i, X18 : $i]:
% 1.02/1.21         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.02/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.21  thf('11', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['9', '10'])).
% 1.02/1.21  thf(t69_enumset1, axiom,
% 1.02/1.21    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.02/1.21  thf('12', plain,
% 1.02/1.21      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['9', '10'])).
% 1.02/1.21  thf('14', plain,
% 1.02/1.21      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.21  thf('15', plain,
% 1.02/1.21      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['13', '14'])).
% 1.02/1.21  thf('16', plain,
% 1.02/1.21      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.21  thf('17', plain,
% 1.02/1.21      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.02/1.21         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.02/1.21          | ((X5) = (X6))
% 1.02/1.21          | ((X5) = (X7))
% 1.02/1.21          | ((X5) = (X8)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.21  thf(d3_tarski, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( r1_tarski @ A @ B ) <=>
% 1.02/1.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.02/1.21  thf('18', plain,
% 1.02/1.21      (![X1 : $i, X3 : $i]:
% 1.02/1.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      (![X17 : $i, X18 : $i]:
% 1.02/1.21         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.02/1.21      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X14 @ X13)
% 1.02/1.21          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.02/1.21          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.21  thf('22', plain,
% 1.02/1.21      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 1.02/1.21         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.02/1.21          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['21'])).
% 1.02/1.21  thf('23', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.21          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['20', '22'])).
% 1.02/1.21  thf('24', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.21          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '23'])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['18', '24'])).
% 1.02/1.21  thf('26', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.21          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.21          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['17', '25'])).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['26'])).
% 1.02/1.21  thf('28', plain,
% 1.02/1.21      (![X1 : $i, X3 : $i]:
% 1.02/1.21         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.02/1.21      inference('sup+', [status(thm)], ['27', '28'])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['29'])).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.02/1.21      inference('sup+', [status(thm)], ['16', '30'])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['26'])).
% 1.02/1.21  thf('33', plain,
% 1.02/1.21      (![X1 : $i, X3 : $i]:
% 1.02/1.21         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('34', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['32', '33'])).
% 1.02/1.21  thf('35', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.21      inference('simplify', [status(thm)], ['34'])).
% 1.02/1.21  thf('36', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['31', '35'])).
% 1.02/1.21  thf('37', plain,
% 1.02/1.21      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.02/1.21      inference('condensation', [status(thm)], ['36'])).
% 1.02/1.21  thf('38', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (r1_tarski @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['15', '37'])).
% 1.02/1.21  thf('39', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (r1_tarski @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k1_tarski @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['12', '38'])).
% 1.02/1.21  thf('40', plain,
% 1.02/1.21      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['11', '39'])).
% 1.02/1.21  thf('41', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.21          | (r2_hidden @ X0 @ X2)
% 1.02/1.21          | ~ (r1_tarski @ X1 @ X2))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('42', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.21          | ~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['40', '41'])).
% 1.02/1.21  thf('43', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['8', '42'])).
% 1.02/1.21  thf(d4_tarski, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.02/1.21       ( ![C:$i]:
% 1.02/1.21         ( ( r2_hidden @ C @ B ) <=>
% 1.02/1.21           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.02/1.21  thf('44', plain,
% 1.02/1.21      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X50 @ X51)
% 1.02/1.21          | ~ (r2_hidden @ X52 @ X50)
% 1.02/1.21          | (r2_hidden @ X52 @ X53)
% 1.02/1.21          | ((X53) != (k3_tarski @ X51)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d4_tarski])).
% 1.02/1.21  thf('45', plain,
% 1.02/1.21      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.02/1.21         ((r2_hidden @ X52 @ (k3_tarski @ X51))
% 1.02/1.21          | ~ (r2_hidden @ X52 @ X50)
% 1.02/1.21          | ~ (r2_hidden @ X50 @ X51))),
% 1.02/1.21      inference('simplify', [status(thm)], ['44'])).
% 1.02/1.21  thf('46', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (~ (r2_hidden @ (k1_tarski @ X0) @ X1)
% 1.02/1.21          | (r2_hidden @ X0 @ (k3_tarski @ X1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['43', '45'])).
% 1.02/1.21  thf('47', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['7', '46'])).
% 1.02/1.21  thf(l51_zfmisc_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.02/1.21  thf('48', plain,
% 1.02/1.21      (![X57 : $i, X58 : $i]:
% 1.02/1.21         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 1.02/1.21      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.02/1.21  thf('49', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['47', '48'])).
% 1.02/1.21  thf('50', plain,
% 1.02/1.21      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('51', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.21          | (r2_hidden @ X0 @ X2)
% 1.02/1.21          | ~ (r1_tarski @ X1 @ X2))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('52', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((r2_hidden @ X0 @ sk_B)
% 1.02/1.21          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['50', '51'])).
% 1.02/1.21  thf('53', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.02/1.21      inference('sup-', [status(thm)], ['49', '52'])).
% 1.02/1.21  thf('54', plain, ($false), inference('demod', [status(thm)], ['0', '53'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.06/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
