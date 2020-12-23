%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cad1EvpwIv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 232 expanded)
%              Number of leaves         :   20 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  625 (2588 expanded)
%              Number of equality atoms :   56 ( 259 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    | ( sk_A != sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_1 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( sk_A = sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('20',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A = sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,
    ( ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,(
    sk_A = sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','27'])).

thf('29',plain,(
    sk_A = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','12','23','33'])).

thf('35',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','29','30','35'])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
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

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('44',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','45'])).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['36','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cad1EvpwIv
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 112 iterations in 0.120s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.58  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.58  thf(t34_zfmisc_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( r2_hidden @
% 0.21/0.58         ( k4_tarski @ A @ B ) @ 
% 0.21/0.58         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.58       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58        ( ( r2_hidden @
% 0.21/0.58            ( k4_tarski @ A @ B ) @ 
% 0.21/0.58            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.58          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((((sk_B) != (sk_D))
% 0.21/0.58        | ((sk_A) != (sk_C_1))
% 0.21/0.58        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58             (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))
% 0.21/0.58         <= (~
% 0.21/0.58             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (~
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))) | 
% 0.21/0.58       ~ (((sk_B) = (sk_D))) | ~ (((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1))
% 0.21/0.58        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf(l54_zfmisc_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.58         ((r2_hidden @ X20 @ X21)
% 0.21/0.58          | ~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23)))),
% 0.21/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf(d1_tarski, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X15 @ X14)
% 0.21/0.58          | ((X15) = (X12))
% 0.21/0.58          | ((X14) != (k1_tarski @ X12)))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X12 : $i, X15 : $i]:
% 0.21/0.58         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1)))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.58  thf('10', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      ((((sk_A) != (sk_A)))
% 0.21/0.58         <= (~ (((sk_A) = (sk_C_1))) & 
% 0.21/0.58             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1))) | 
% 0.21/0.58       ~
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1)))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '8'])).
% 0.21/0.58  thf(t69_enumset1, axiom,
% 0.21/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_D))))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.58         ((r2_hidden @ X22 @ X23)
% 0.21/0.58          | ~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X23)))),
% 0.21/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X12 : $i, X15 : $i]:
% 0.21/0.58         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      ((((sk_B) = (sk_D)))
% 0.21/0.58         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf('21', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.21/0.58      inference('split', [status(esa)], ['0'])).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      ((((sk_B) != (sk_B)))
% 0.21/0.58         <= (~ (((sk_B) = (sk_D))) & 
% 0.21/0.58             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58               (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      ((((sk_B) = (sk_D))) | 
% 0.21/0.58       ~
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (~
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['2', '12', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D)))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.21/0.58  thf('26', plain, ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (sk_C_1))))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      ((((sk_A) = (sk_C_1))) | 
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('28', plain, ((((sk_A) = (sk_C_1)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '27'])).
% 0.21/0.58  thf('29', plain, (((sk_A) = (sk_C_1))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      ((((sk_B) = (sk_D))
% 0.21/0.58        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58           (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('32', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.21/0.58      inference('split', [status(esa)], ['31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      ((((sk_B) = (sk_D))) | 
% 0.21/0.58       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58         (k2_zfmisc_1 @ (k1_tarski @ sk_C_1) @ (k1_tarski @ sk_D))))),
% 0.21/0.58      inference('split', [status(esa)], ['31'])).
% 0.21/0.58  thf('34', plain, ((((sk_B) = (sk_D)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '33'])).
% 0.21/0.58  thf('35', plain, (((sk_B) = (sk_D))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.21/0.58      inference('demod', [status(thm)], ['25', '29', '30', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.58  thf(t70_enumset1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]:
% 0.21/0.58         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.58  thf(d1_enumset1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.58       ( ![E:$i]:
% 0.21/0.58         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.58           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_2, axiom,
% 0.21/0.58    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.58       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_3, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.58     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.58       ( ![E:$i]:
% 0.21/0.58         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.58         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.21/0.58          | (r2_hidden @ X5 @ X9)
% 0.21/0.58          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.58         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.21/0.58          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.21/0.58      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.58          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['39', '41'])).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.58         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.21/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['42', '44'])).
% 0.21/0.58  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['38', '45'])).
% 0.21/0.58  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['38', '45'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.21/0.58         ((r2_hidden @ (k4_tarski @ X20 @ X22) @ (k2_zfmisc_1 @ X21 @ X24))
% 0.21/0.58          | ~ (r2_hidden @ X22 @ X24)
% 0.21/0.58          | ~ (r2_hidden @ X20 @ X21))),
% 0.21/0.58      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X2 @ X1)
% 0.21/0.58          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.21/0.58             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.21/0.58          (k2_zfmisc_1 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['37', '50'])).
% 0.21/0.58  thf('52', plain, ($false), inference('demod', [status(thm)], ['36', '51'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
