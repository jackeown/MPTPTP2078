%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dv17DpheAC

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 228 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   26
%              Number of atoms          :  747 (3083 expanded)
%              Number of equality atoms :  132 ( 490 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t19_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( ( k2_mcart_1 @ A )
            = D )
          | ( ( k2_mcart_1 @ A )
            = E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( ( k2_mcart_1 @ A )
              = D )
            | ( ( k2_mcart_1 @ A )
              = E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_enumset1 @ sk_B @ sk_B @ sk_C ) @ ( k2_tarski @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 )
      | ( X10 = X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t146_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
      = ( k2_enumset1 @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X5 @ X8 ) @ ( k2_tarski @ X6 @ X7 ) )
      = ( k2_enumset1 @ ( k4_tarski @ X5 @ X6 ) @ ( k4_tarski @ X5 @ X7 ) @ ( k4_tarski @ X8 @ X6 ) @ ( k4_tarski @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t146_zfmisc_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X16 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X16 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k2_enumset1 @ X19 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k2_tarski @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( zip_tseitin_0 @ X4 @ ( k4_tarski @ X2 @ X0 ) @ ( k4_tarski @ X2 @ X1 ) @ ( k4_tarski @ X3 @ X0 ) @ ( k4_tarski @ X3 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k4_tarski @ X1 @ X0 ) )
      | ( X4
        = ( k4_tarski @ X1 @ X2 ) )
      | ( X4
        = ( k4_tarski @ X3 @ X0 ) )
      | ( X4
        = ( k4_tarski @ X3 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X3 ) @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ ( k2_tarski @ X3 @ X2 ) ) )
      | ( X4
        = ( k4_tarski @ X0 @ X2 ) )
      | ( X4
        = ( k4_tarski @ X0 @ X3 ) )
      | ( X4
        = ( k4_tarski @ X1 @ X2 ) )
      | ( X4
        = ( k4_tarski @ X1 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('14',plain,(
    ! [X23: $i,X25: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('15',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X23: $i,X25: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('21',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
    | ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( sk_A
      = ( k4_tarski @ sk_C @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('27',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('30',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('35',plain,
    ( ( ( sk_C != sk_C )
      | ( ( k1_mcart_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('38',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['20','22','39'])).

thf('41',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['19','40'])).

thf('42',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_E ) )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['17','41'])).

thf('43',plain,(
    ! [X23: $i,X25: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('44',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_D ) )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X23: $i,X25: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('47',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_D )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_E ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_mcart_1 @ sk_A )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['19','40'])).

thf('49',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_E ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( sk_E != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_E ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['50'])).

thf('55',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dv17DpheAC
% 0.17/0.38  % Computer   : n019.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 16:57:38 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.63/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.63/0.80  % Solved by: fo/fo7.sh
% 0.63/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.80  % done 291 iterations in 0.302s
% 0.63/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.63/0.80  % SZS output start Refutation
% 0.63/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.80  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.63/0.80  thf(sk_C_type, type, sk_C: $i).
% 0.63/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.63/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.63/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.80  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.63/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.63/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.63/0.80  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.63/0.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.63/0.80  thf(sk_E_type, type, sk_E: $i).
% 0.63/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.63/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.63/0.80  thf(t19_mcart_1, conjecture,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.63/0.80     ( ( r2_hidden @
% 0.63/0.80         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.63/0.80       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.63/0.80         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.63/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.80    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.63/0.80        ( ( r2_hidden @
% 0.63/0.80            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.63/0.80          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.63/0.80            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.63/0.80    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.63/0.80  thf('0', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('1', plain,
% 0.63/0.80      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('split', [status(esa)], ['0'])).
% 0.63/0.80  thf('2', plain,
% 0.63/0.80      ((r2_hidden @ sk_A @ 
% 0.63/0.80        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k2_tarski @ sk_D @ sk_E)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf(t70_enumset1, axiom,
% 0.63/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.63/0.80  thf('3', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i]:
% 0.63/0.80         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.63/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.63/0.80  thf('4', plain,
% 0.63/0.80      ((r2_hidden @ sk_A @ 
% 0.63/0.80        (k2_zfmisc_1 @ (k1_enumset1 @ sk_B @ sk_B @ sk_C) @ 
% 0.63/0.80         (k2_tarski @ sk_D @ sk_E)))),
% 0.63/0.80      inference('demod', [status(thm)], ['2', '3'])).
% 0.63/0.80  thf('5', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i]:
% 0.63/0.80         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X0 @ X1))),
% 0.63/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.63/0.80  thf(d2_enumset1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.63/0.80     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.63/0.80       ( ![F:$i]:
% 0.63/0.80         ( ( r2_hidden @ F @ E ) <=>
% 0.63/0.80           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 0.63/0.80                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 0.63/0.80  thf(zf_stmt_1, axiom,
% 0.63/0.80    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 0.63/0.80     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 0.63/0.80       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 0.63/0.80         ( ( F ) != ( D ) ) ) ))).
% 0.63/0.80  thf('6', plain,
% 0.63/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.63/0.80         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.63/0.80          | ((X10) = (X11))
% 0.63/0.80          | ((X10) = (X12))
% 0.63/0.80          | ((X10) = (X13))
% 0.63/0.80          | ((X10) = (X14)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.63/0.80  thf(t146_zfmisc_1, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.63/0.80     ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) =
% 0.63/0.80       ( k2_enumset1 @
% 0.63/0.80         ( k4_tarski @ A @ C ) @ ( k4_tarski @ A @ D ) @ 
% 0.63/0.80         ( k4_tarski @ B @ C ) @ ( k4_tarski @ B @ D ) ) ))).
% 0.63/0.80  thf('7', plain,
% 0.63/0.80      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.63/0.80         ((k2_zfmisc_1 @ (k2_tarski @ X5 @ X8) @ (k2_tarski @ X6 @ X7))
% 0.63/0.80           = (k2_enumset1 @ (k4_tarski @ X5 @ X6) @ (k4_tarski @ X5 @ X7) @ 
% 0.63/0.80              (k4_tarski @ X8 @ X6) @ (k4_tarski @ X8 @ X7)))),
% 0.63/0.80      inference('cnf', [status(esa)], [t146_zfmisc_1])).
% 0.63/0.80  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.63/0.80  thf(zf_stmt_3, axiom,
% 0.63/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.63/0.80     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 0.63/0.80       ( ![F:$i]:
% 0.63/0.80         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 0.63/0.80  thf('8', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.63/0.80         (~ (r2_hidden @ X21 @ X20)
% 0.63/0.80          | ~ (zip_tseitin_0 @ X21 @ X16 @ X17 @ X18 @ X19)
% 0.63/0.80          | ((X20) != (k2_enumset1 @ X19 @ X18 @ X17 @ X16)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.63/0.80  thf('9', plain,
% 0.63/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.63/0.80         (~ (zip_tseitin_0 @ X21 @ X16 @ X17 @ X18 @ X19)
% 0.63/0.80          | ~ (r2_hidden @ X21 @ (k2_enumset1 @ X19 @ X18 @ X17 @ X16)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.63/0.80  thf('10', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.63/0.80         (~ (r2_hidden @ X4 @ 
% 0.63/0.80             (k2_zfmisc_1 @ (k2_tarski @ X3 @ X2) @ (k2_tarski @ X1 @ X0)))
% 0.63/0.80          | ~ (zip_tseitin_0 @ X4 @ (k4_tarski @ X2 @ X0) @ 
% 0.63/0.80               (k4_tarski @ X2 @ X1) @ (k4_tarski @ X3 @ X0) @ 
% 0.63/0.80               (k4_tarski @ X3 @ X1)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['7', '9'])).
% 0.63/0.80  thf('11', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.63/0.80         (((X4) = (k4_tarski @ X1 @ X0))
% 0.63/0.80          | ((X4) = (k4_tarski @ X1 @ X2))
% 0.63/0.80          | ((X4) = (k4_tarski @ X3 @ X0))
% 0.63/0.80          | ((X4) = (k4_tarski @ X3 @ X2))
% 0.63/0.80          | ~ (r2_hidden @ X4 @ 
% 0.63/0.80               (k2_zfmisc_1 @ (k2_tarski @ X1 @ X3) @ (k2_tarski @ X0 @ X2))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['6', '10'])).
% 0.63/0.80  thf('12', plain,
% 0.63/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.63/0.80         (~ (r2_hidden @ X4 @ 
% 0.63/0.80             (k2_zfmisc_1 @ (k1_enumset1 @ X1 @ X1 @ X0) @ 
% 0.63/0.80              (k2_tarski @ X3 @ X2)))
% 0.63/0.80          | ((X4) = (k4_tarski @ X0 @ X2))
% 0.63/0.80          | ((X4) = (k4_tarski @ X0 @ X3))
% 0.63/0.80          | ((X4) = (k4_tarski @ X1 @ X2))
% 0.63/0.80          | ((X4) = (k4_tarski @ X1 @ X3)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['5', '11'])).
% 0.63/0.80  thf('13', plain,
% 0.63/0.80      ((((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_E)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['4', '12'])).
% 0.63/0.80  thf(t7_mcart_1, axiom,
% 0.63/0.80    (![A:$i,B:$i]:
% 0.63/0.80     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.63/0.80       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.63/0.80  thf('14', plain,
% 0.63/0.80      (![X23 : $i, X25 : $i]: ((k2_mcart_1 @ (k4_tarski @ X23 @ X25)) = (X25))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('15', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) = (sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['13', '14'])).
% 0.63/0.80  thf('16', plain,
% 0.63/0.80      (![X23 : $i, X25 : $i]: ((k2_mcart_1 @ (k4_tarski @ X23 @ X25)) = (X25))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('17', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) = (sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['15', '16'])).
% 0.63/0.80  thf('18', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('19', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.63/0.80         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.63/0.80      inference('split', [status(esa)], ['18'])).
% 0.63/0.80  thf('20', plain,
% 0.63/0.80      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.63/0.80      inference('split', [status(esa)], ['18'])).
% 0.63/0.80  thf('21', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('22', plain,
% 0.63/0.80      (~ (((k2_mcart_1 @ sk_A) = (sk_D))) | ~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.63/0.80      inference('split', [status(esa)], ['21'])).
% 0.63/0.80  thf('23', plain,
% 0.63/0.80      ((((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_E)))),
% 0.63/0.80      inference('sup-', [status(thm)], ['4', '12'])).
% 0.63/0.80  thf('24', plain,
% 0.63/0.80      (![X23 : $i, X24 : $i]: ((k1_mcart_1 @ (k4_tarski @ X23 @ X24)) = (X23))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('25', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_C))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_C @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.63/0.80  thf('26', plain,
% 0.63/0.80      (![X23 : $i, X24 : $i]: ((k1_mcart_1 @ (k4_tarski @ X23 @ X24)) = (X23))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('27', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_C))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['25', '26'])).
% 0.63/0.80  thf('28', plain,
% 0.63/0.80      ((((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['27'])).
% 0.63/0.80  thf('29', plain,
% 0.63/0.80      (![X23 : $i, X24 : $i]: ((k1_mcart_1 @ (k4_tarski @ X23 @ X24)) = (X23))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('30', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.63/0.80        | ((k1_mcart_1 @ sk_A) = (sk_C))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['28', '29'])).
% 0.63/0.80  thf('31', plain,
% 0.63/0.80      (![X23 : $i, X24 : $i]: ((k1_mcart_1 @ (k4_tarski @ X23 @ X24)) = (X23))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('32', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_B))
% 0.63/0.80        | ((k1_mcart_1 @ sk_A) = (sk_C))
% 0.63/0.80        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['30', '31'])).
% 0.63/0.80  thf('33', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['32'])).
% 0.63/0.80  thf('34', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.63/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.63/0.80      inference('split', [status(esa)], ['21'])).
% 0.63/0.80  thf('35', plain,
% 0.63/0.80      (((((sk_C) != (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B))))
% 0.63/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['33', '34'])).
% 0.63/0.80  thf('36', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.63/0.80      inference('simplify', [status(thm)], ['35'])).
% 0.63/0.80  thf('37', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.63/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.63/0.80      inference('split', [status(esa)], ['18'])).
% 0.63/0.80  thf('38', plain,
% 0.63/0.80      ((((sk_B) != (sk_B)))
% 0.63/0.80         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 0.63/0.80             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['36', '37'])).
% 0.63/0.80  thf('39', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['38'])).
% 0.63/0.80  thf('40', plain, (~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['20', '22', '39'])).
% 0.63/0.80  thf('41', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['19', '40'])).
% 0.63/0.80  thf('42', plain,
% 0.63/0.80      ((((sk_A) = (k4_tarski @ sk_B @ sk_D))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_E))
% 0.63/0.80        | ((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['17', '41'])).
% 0.63/0.80  thf('43', plain,
% 0.63/0.80      (![X23 : $i, X25 : $i]: ((k2_mcart_1 @ (k4_tarski @ X23 @ X25)) = (X25))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('44', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) = (sk_E))
% 0.63/0.80        | ((k2_mcart_1 @ sk_A) = (sk_E))
% 0.63/0.80        | ((sk_A) = (k4_tarski @ sk_B @ sk_D)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['42', '43'])).
% 0.63/0.80  thf('45', plain,
% 0.63/0.80      ((((sk_A) = (k4_tarski @ sk_B @ sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['44'])).
% 0.63/0.80  thf('46', plain,
% 0.63/0.80      (![X23 : $i, X25 : $i]: ((k2_mcart_1 @ (k4_tarski @ X23 @ X25)) = (X25))),
% 0.63/0.80      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.63/0.80  thf('47', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) = (sk_D)) | ((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('sup+', [status(thm)], ['45', '46'])).
% 0.63/0.80  thf('48', plain, (((k2_mcart_1 @ sk_A) != (sk_D))),
% 0.63/0.80      inference('simpl_trail', [status(thm)], ['19', '40'])).
% 0.63/0.80  thf('49', plain, (((k2_mcart_1 @ sk_A) = (sk_E))),
% 0.63/0.80      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.63/0.80  thf('50', plain,
% 0.63/0.80      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.63/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.80  thf('51', plain,
% 0.63/0.80      ((((k2_mcart_1 @ sk_A) != (sk_E)))
% 0.63/0.80         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.63/0.80      inference('split', [status(esa)], ['50'])).
% 0.63/0.80  thf('52', plain,
% 0.63/0.80      ((((sk_E) != (sk_E))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.63/0.80      inference('sup-', [status(thm)], ['49', '51'])).
% 0.63/0.80  thf('53', plain, ((((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('simplify', [status(thm)], ['52'])).
% 0.63/0.80  thf('54', plain,
% 0.63/0.80      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.63/0.80      inference('split', [status(esa)], ['50'])).
% 0.63/0.80  thf('55', plain, ($false),
% 0.63/0.80      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '39'])).
% 0.63/0.80  
% 0.63/0.80  % SZS output end Refutation
% 0.63/0.80  
% 0.63/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
