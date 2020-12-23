%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kv99VMID5c

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:58 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 114 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   22
%              Number of atoms          :  616 ( 957 expanded)
%              Number of equality atoms :   37 (  68 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X22 @ X22 @ X23 @ X24 )
      = ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_enumset1 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
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
      | ~ ( r2_hidden @ X1 @ ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('46',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X47 @ X48 )
      | ~ ( r2_hidden @ X49 @ X47 )
      | ( r2_hidden @ X49 @ X50 )
      | ( X50
       != ( k3_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('47',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( r2_hidden @ X49 @ ( k3_tarski @ X48 ) )
      | ~ ( r2_hidden @ X49 @ X47 )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','48'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('50',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kv99VMID5c
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.88/2.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.88/2.08  % Solved by: fo/fo7.sh
% 1.88/2.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.88/2.08  % done 893 iterations in 1.637s
% 1.88/2.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.88/2.08  % SZS output start Refutation
% 1.88/2.08  thf(sk_B_type, type, sk_B: $i).
% 1.88/2.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.88/2.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.88/2.08  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.88/2.08  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.88/2.08  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.88/2.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.88/2.08  thf(sk_A_type, type, sk_A: $i).
% 1.88/2.08  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.88/2.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.88/2.08  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.88/2.08  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.88/2.08  thf(t45_zfmisc_1, conjecture,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.88/2.09       ( r2_hidden @ A @ B ) ))).
% 1.88/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.88/2.09    (~( ![A:$i,B:$i]:
% 1.88/2.09        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 1.88/2.09          ( r2_hidden @ A @ B ) ) )),
% 1.88/2.09    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 1.88/2.09  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.09  thf(t70_enumset1, axiom,
% 1.88/2.09    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.88/2.09  thf('1', plain,
% 1.88/2.09      (![X20 : $i, X21 : $i]:
% 1.88/2.09         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 1.88/2.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.88/2.09  thf(d1_enumset1, axiom,
% 1.88/2.09    (![A:$i,B:$i,C:$i,D:$i]:
% 1.88/2.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.88/2.09       ( ![E:$i]:
% 1.88/2.09         ( ( r2_hidden @ E @ D ) <=>
% 1.88/2.09           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.88/2.09  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.88/2.09  thf(zf_stmt_2, axiom,
% 1.88/2.09    (![E:$i,C:$i,B:$i,A:$i]:
% 1.88/2.09     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.88/2.09       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.88/2.09  thf(zf_stmt_3, axiom,
% 1.88/2.09    (![A:$i,B:$i,C:$i,D:$i]:
% 1.88/2.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.88/2.09       ( ![E:$i]:
% 1.88/2.09         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.88/2.09  thf('2', plain,
% 1.88/2.09      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.88/2.09         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 1.88/2.09          | (r2_hidden @ X9 @ X13)
% 1.88/2.09          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.88/2.09  thf('3', plain,
% 1.88/2.09      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.88/2.09         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 1.88/2.09          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 1.88/2.09      inference('simplify', [status(thm)], ['2'])).
% 1.88/2.09  thf('4', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.09         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.88/2.09          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.88/2.09      inference('sup+', [status(thm)], ['1', '3'])).
% 1.88/2.09  thf('5', plain,
% 1.88/2.09      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.88/2.09         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.88/2.09  thf('6', plain,
% 1.88/2.09      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 1.88/2.09      inference('simplify', [status(thm)], ['5'])).
% 1.88/2.09  thf('7', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.88/2.09      inference('sup-', [status(thm)], ['4', '6'])).
% 1.88/2.09  thf(t71_enumset1, axiom,
% 1.88/2.09    (![A:$i,B:$i,C:$i]:
% 1.88/2.09     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.88/2.09  thf('8', plain,
% 1.88/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.88/2.09         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 1.88/2.09           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 1.88/2.09      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.88/2.09  thf('9', plain,
% 1.88/2.09      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.88/2.09         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 1.88/2.09          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 1.88/2.09      inference('simplify', [status(thm)], ['2'])).
% 1.88/2.09  thf('10', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.88/2.09         ((r2_hidden @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.88/2.09          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2))),
% 1.88/2.09      inference('sup+', [status(thm)], ['8', '9'])).
% 1.88/2.09  thf(t69_enumset1, axiom,
% 1.88/2.09    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.88/2.09  thf('11', plain,
% 1.88/2.09      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 1.88/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.88/2.09  thf('12', plain,
% 1.88/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.88/2.09         ((k2_enumset1 @ X22 @ X22 @ X23 @ X24)
% 1.88/2.09           = (k1_enumset1 @ X22 @ X23 @ X24))),
% 1.88/2.09      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.88/2.09  thf('13', plain,
% 1.88/2.09      (![X20 : $i, X21 : $i]:
% 1.88/2.09         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 1.88/2.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.88/2.09  thf('14', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.88/2.09      inference('sup+', [status(thm)], ['12', '13'])).
% 1.88/2.09  thf('15', plain,
% 1.88/2.09      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 1.88/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.88/2.09  thf('16', plain,
% 1.88/2.09      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.88/2.09      inference('sup+', [status(thm)], ['14', '15'])).
% 1.88/2.09  thf('17', plain,
% 1.88/2.09      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 1.88/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.88/2.09  thf('18', plain,
% 1.88/2.09      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.88/2.09         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 1.88/2.09          | ((X5) = (X6))
% 1.88/2.09          | ((X5) = (X7))
% 1.88/2.09          | ((X5) = (X8)))),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.88/2.09  thf(d3_tarski, axiom,
% 1.88/2.09    (![A:$i,B:$i]:
% 1.88/2.09     ( ( r1_tarski @ A @ B ) <=>
% 1.88/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.88/2.09  thf('19', plain,
% 1.88/2.09      (![X1 : $i, X3 : $i]:
% 1.88/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.88/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.09  thf('20', plain,
% 1.88/2.09      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 1.88/2.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.88/2.09  thf('21', plain,
% 1.88/2.09      (![X20 : $i, X21 : $i]:
% 1.88/2.09         ((k1_enumset1 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 1.88/2.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.88/2.09  thf('22', plain,
% 1.88/2.09      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X14 @ X13)
% 1.88/2.09          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.88/2.09          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.88/2.09  thf('23', plain,
% 1.88/2.09      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 1.88/2.09         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 1.88/2.09          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 1.88/2.09      inference('simplify', [status(thm)], ['22'])).
% 1.88/2.09  thf('24', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.88/2.09          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.88/2.09      inference('sup-', [status(thm)], ['21', '23'])).
% 1.88/2.09  thf('25', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.88/2.09          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.88/2.09      inference('sup-', [status(thm)], ['20', '24'])).
% 1.88/2.09  thf('26', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.88/2.09      inference('sup-', [status(thm)], ['19', '25'])).
% 1.88/2.09  thf('27', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.88/2.09          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.88/2.09          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.88/2.09      inference('sup-', [status(thm)], ['18', '26'])).
% 1.88/2.09  thf('28', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.88/2.09      inference('simplify', [status(thm)], ['27'])).
% 1.88/2.09  thf('29', plain,
% 1.88/2.09      (![X1 : $i, X3 : $i]:
% 1.88/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.88/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.09  thf('30', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.88/2.09      inference('sup+', [status(thm)], ['28', '29'])).
% 1.88/2.09  thf('31', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.88/2.09      inference('simplify', [status(thm)], ['30'])).
% 1.88/2.09  thf('32', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.88/2.09      inference('sup+', [status(thm)], ['17', '31'])).
% 1.88/2.09  thf('33', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.88/2.09      inference('simplify', [status(thm)], ['27'])).
% 1.88/2.09  thf('34', plain,
% 1.88/2.09      (![X1 : $i, X3 : $i]:
% 1.88/2.09         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.88/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.09  thf('35', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 1.88/2.09      inference('sup-', [status(thm)], ['33', '34'])).
% 1.88/2.09  thf('36', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.88/2.09      inference('simplify', [status(thm)], ['35'])).
% 1.88/2.09  thf('37', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['32', '36'])).
% 1.88/2.09  thf('38', plain,
% 1.88/2.09      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.88/2.09      inference('condensation', [status(thm)], ['37'])).
% 1.88/2.09  thf('39', plain,
% 1.88/2.09      (![X0 : $i]:
% 1.88/2.09         (r1_tarski @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k2_tarski @ X0 @ X0))),
% 1.88/2.09      inference('sup+', [status(thm)], ['16', '38'])).
% 1.88/2.09  thf('40', plain,
% 1.88/2.09      (![X0 : $i]:
% 1.88/2.09         (r1_tarski @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0) @ (k1_tarski @ X0))),
% 1.88/2.09      inference('sup+', [status(thm)], ['11', '39'])).
% 1.88/2.09  thf('41', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.88/2.09          | (r2_hidden @ X0 @ X2)
% 1.88/2.09          | ~ (r1_tarski @ X1 @ X2))),
% 1.88/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.09  thf('42', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.88/2.09          | ~ (r2_hidden @ X1 @ (k2_enumset1 @ X0 @ X0 @ X0 @ X0)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['40', '41'])).
% 1.88/2.09  thf('43', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         ((zip_tseitin_0 @ X1 @ X0 @ X0 @ X0)
% 1.88/2.09          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['10', '42'])).
% 1.88/2.09  thf('44', plain,
% 1.88/2.09      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 1.88/2.09      inference('simplify', [status(thm)], ['5'])).
% 1.88/2.09  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.88/2.09      inference('sup-', [status(thm)], ['43', '44'])).
% 1.88/2.09  thf(d4_tarski, axiom,
% 1.88/2.09    (![A:$i,B:$i]:
% 1.88/2.09     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.88/2.09       ( ![C:$i]:
% 1.88/2.09         ( ( r2_hidden @ C @ B ) <=>
% 1.88/2.09           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.88/2.09  thf('46', plain,
% 1.88/2.09      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X47 @ X48)
% 1.88/2.09          | ~ (r2_hidden @ X49 @ X47)
% 1.88/2.09          | (r2_hidden @ X49 @ X50)
% 1.88/2.09          | ((X50) != (k3_tarski @ X48)))),
% 1.88/2.09      inference('cnf', [status(esa)], [d4_tarski])).
% 1.88/2.09  thf('47', plain,
% 1.88/2.09      (![X47 : $i, X48 : $i, X49 : $i]:
% 1.88/2.09         ((r2_hidden @ X49 @ (k3_tarski @ X48))
% 1.88/2.09          | ~ (r2_hidden @ X49 @ X47)
% 1.88/2.09          | ~ (r2_hidden @ X47 @ X48))),
% 1.88/2.09      inference('simplify', [status(thm)], ['46'])).
% 1.88/2.09  thf('48', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (~ (r2_hidden @ (k1_tarski @ X0) @ X1)
% 1.88/2.09          | (r2_hidden @ X0 @ (k3_tarski @ X1)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['45', '47'])).
% 1.88/2.09  thf('49', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ (k1_tarski @ X1) @ X0)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['7', '48'])).
% 1.88/2.09  thf(l51_zfmisc_1, axiom,
% 1.88/2.09    (![A:$i,B:$i]:
% 1.88/2.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.88/2.09  thf('50', plain,
% 1.88/2.09      (![X54 : $i, X55 : $i]:
% 1.88/2.09         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 1.88/2.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.88/2.09  thf('51', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i]:
% 1.88/2.09         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.88/2.09      inference('demod', [status(thm)], ['49', '50'])).
% 1.88/2.09  thf('52', plain,
% 1.88/2.09      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 1.88/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.09  thf('53', plain,
% 1.88/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.88/2.09          | (r2_hidden @ X0 @ X2)
% 1.88/2.09          | ~ (r1_tarski @ X1 @ X2))),
% 1.88/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.09  thf('54', plain,
% 1.88/2.09      (![X0 : $i]:
% 1.88/2.09         ((r2_hidden @ X0 @ sk_B)
% 1.88/2.09          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.88/2.09      inference('sup-', [status(thm)], ['52', '53'])).
% 1.88/2.09  thf('55', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.88/2.09      inference('sup-', [status(thm)], ['51', '54'])).
% 1.88/2.09  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 1.88/2.09  
% 1.88/2.09  % SZS output end Refutation
% 1.88/2.09  
% 1.88/2.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
