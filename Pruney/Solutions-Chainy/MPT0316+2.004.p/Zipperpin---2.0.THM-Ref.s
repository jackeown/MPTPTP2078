%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIGWvHvJlk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  579 ( 985 expanded)
%              Number of equality atoms :   39 (  69 expanded)
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

thf(t128_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
      <=> ( ( A = C )
          & ( r2_hidden @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
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

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X22 ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( r2_hidden @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['6'])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ ( k2_zfmisc_1 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_A = sk_C )
      | ( sk_A = sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('42',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D ) )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','8','9','26','27','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pIGWvHvJlk
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 61 iterations in 0.028s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(t128_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @
% 0.20/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( r2_hidden @
% 0.20/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D)
% 0.20/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((sk_A) = (sk_C))
% 0.20/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf(l54_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.48         ((r2_hidden @ X20 @ X21)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X21)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.20/0.48        | ((sk_A) != (sk_C))
% 0.20/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (~ (((sk_A) = (sk_C))) | 
% 0.20/0.48       ~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf(t70_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf(d1_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.48       ( ![E:$i]:
% 0.20/0.48         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.48           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_2, axiom,
% 0.20/0.48    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.48       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.48       ( ![E:$i]:
% 0.20/0.48         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.48          | (r2_hidden @ X5 @ X9)
% 0.20/0.48          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.20/0.48          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.48          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['11', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.48  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X22))
% 0.20/0.48          | ~ (r2_hidden @ X20 @ X22)
% 0.20/0.48          | ~ (r2_hidden @ X18 @ X19))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (~ (r2_hidden @ X1 @ X0)
% 0.20/0.48           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D))))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D)))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.48  thf('23', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) & 
% 0.20/0.48             (((sk_A) = (sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       ~ (((sk_A) = (sk_C))) | ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       (((sk_A) = (sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.20/0.48          | ((X1) = (X2))
% 0.20/0.48          | ((X1) = (X3))
% 0.20/0.48          | ((X1) = (X4)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('split', [status(esa)], ['2'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.48         ((r2_hidden @ X18 @ X19)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ (k2_zfmisc_1 @ X19 @ X21)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.48          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.48          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.20/0.48         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.20/0.48          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.48          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_C))))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((((sk_A) = (sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.48  thf('41', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['6'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)))
% 0.20/0.48         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D))) | 
% 0.20/0.48       (((sk_A) = (sk_C)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.48  thf('44', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['1', '8', '9', '26', '27', '43'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
