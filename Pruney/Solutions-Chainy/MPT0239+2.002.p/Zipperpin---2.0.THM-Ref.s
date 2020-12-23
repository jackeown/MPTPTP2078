%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hvOTE5ysEi

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 249 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  703 (2794 expanded)
%              Number of equality atoms :   63 ( 280 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t34_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
      <=> ( ( A = C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_A = sk_C )
      | ( sk_A = sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('25',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ sk_D @ sk_D @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( sk_B = sk_D )
      | ( sk_B = sk_D )
      | ( sk_B = sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','19','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,(
    sk_A = sk_C ),
    inference('sat_resolution*',[status(thm)],['2','19','30','34'])).

thf('36',plain,(
    sk_A = sk_C ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('41',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','19','30','40'])).

thf('42',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf('54',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X22 ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['43','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['32','36','37','42','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hvOTE5ysEi
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:05:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 96 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(t34_zfmisc_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( r2_hidden @
% 0.22/0.49         ( k4_tarski @ A @ B ) @ 
% 0.22/0.49         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49        ( ( r2_hidden @
% 0.22/0.49            ( k4_tarski @ A @ B ) @ 
% 0.22/0.49            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.49          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((((sk_B) != (sk_D))
% 0.22/0.49        | ((sk_A) != (sk_C))
% 0.22/0.49        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.49         <= (~
% 0.22/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.49       ~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(d1_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.49       ( ![E:$i]:
% 0.22/0.49         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.49           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_1, axiom,
% 0.22/0.49    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.49       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.22/0.49          | ((X1) = (X2))
% 0.22/0.49          | ((X1) = (X3))
% 0.22/0.49          | ((X1) = (X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((((sk_A) = (sk_C))
% 0.22/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf(l54_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         ((r2_hidden @ X18 @ X19)
% 0.22/0.49          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('8', plain, (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t70_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.49  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_3, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.49       ( ![E:$i]:
% 0.22/0.49         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.49          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.22/0.49          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.49         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.22/0.49          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.49          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_C))))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((((sk_A) = (sk_C)))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.49  thf('17', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((sk_A) != (sk_A)))
% 0.22/0.49         <= (~ (((sk_A) = (sk_C))) & 
% 0.22/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((((sk_A) = (sk_C))) | 
% 0.22/0.49       ~
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.22/0.49          | ((X1) = (X2))
% 0.22/0.49          | ((X1) = (X3))
% 0.22/0.49          | ((X1) = (X4)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.49         ((r2_hidden @ X20 @ X21)
% 0.22/0.49          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X21)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.49          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '12'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((~ (zip_tseitin_0 @ sk_B @ sk_D @ sk_D @ sk_D))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((((sk_B) = (sk_D)) | ((sk_B) = (sk_D)) | ((sk_B) = (sk_D))))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((((sk_B) = (sk_D)))
% 0.22/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.49  thf('28', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((sk_B) != (sk_B)))
% 0.22/0.49         <= (~ (((sk_B) = (sk_D))) & 
% 0.22/0.49             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((((sk_B) = (sk_D))) | 
% 0.22/0.49       ~
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '19', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49          (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.22/0.49  thf('33', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((((sk_A) = (sk_C))) | 
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['4'])).
% 0.22/0.49  thf('35', plain, ((((sk_A) = (sk_C)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '19', '30', '34'])).
% 0.22/0.49  thf('36', plain, (((sk_A) = (sk_C))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((sk_B) = (sk_D))
% 0.22/0.49        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((((sk_B) = (sk_D))) | 
% 0.22/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.49      inference('split', [status(esa)], ['38'])).
% 0.22/0.49  thf('41', plain, ((((sk_B) = (sk_D)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '19', '30', '40'])).
% 0.22/0.49  thf('42', plain, (((sk_B) = (sk_D))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.22/0.49          | (r2_hidden @ X5 @ X9)
% 0.22/0.49          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.22/0.49          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.22/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.49          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['45', '47'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.49         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.22/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '50'])).
% 0.22/0.49  thf('52', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['44', '51'])).
% 0.22/0.49  thf('53', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['44', '51'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.22/0.49         ((r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X22))
% 0.22/0.49          | ~ (r2_hidden @ X20 @ X22)
% 0.22/0.49          | ~ (r2_hidden @ X18 @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X2 @ X1)
% 0.22/0.49          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.22/0.49             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.22/0.49          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['52', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.22/0.49          (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['43', '56'])).
% 0.22/0.49  thf('58', plain, ($false),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '36', '37', '42', '57'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
