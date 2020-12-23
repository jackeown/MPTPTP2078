%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U13DgHZFws

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 193 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  529 (2108 expanded)
%              Number of equality atoms :   37 ( 141 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( sk_A = sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X54 @ X55 )
      | ~ ( r2_hidden @ ( k4_tarski @ X54 @ X56 ) @ ( k2_zfmisc_1 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C_3 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = sk_C_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( sk_A != sk_C_3 )
   <= ( sk_A != sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C_3 )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( sk_A = sk_C_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ X57 )
      | ~ ( r2_hidden @ ( k4_tarski @ X54 @ X56 ) @ ( k2_zfmisc_1 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('17',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
   <= ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['2','12','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,
    ( ( sk_A = sk_C_3 )
   <= ( sk_A = sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,
    ( ( sk_A = sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['3'])).

thf('24',plain,(
    sk_A = sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['2','12','19','23'])).

thf('25',plain,(
    sk_A = sk_C_3 ),
    inference(simpl_trail,[status(thm)],['22','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','25'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

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

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C_3 ) @ sk_D ) ) ),
    inference(split,[status(esa)],['36'])).

thf('39',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','12','19','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X54: $i,X55: $i,X56: $i,X58: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X54 @ X56 ) @ ( k2_zfmisc_1 @ X55 @ X58 ) )
      | ~ ( r2_hidden @ X56 @ X58 )
      | ~ ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['26','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U13DgHZFws
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 16:10:24 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 316 iterations in 0.147s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(t128_zfmisc_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( r2_hidden @
% 0.45/0.63         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.45/0.63       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63        ( ( r2_hidden @
% 0.45/0.63            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.45/0.63          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.45/0.63        | ((sk_A) != (sk_C_3))
% 0.45/0.63        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63             (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))
% 0.45/0.63         <= (~
% 0.45/0.63             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      (~
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))) | 
% 0.45/0.63       ~ ((r2_hidden @ sk_B @ sk_D)) | ~ (((sk_A) = (sk_C_3)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      ((((sk_A) = (sk_C_3))
% 0.45/0.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('split', [status(esa)], ['3'])).
% 0.45/0.63  thf(t106_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.45/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.45/0.63         ((r2_hidden @ X54 @ X55)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X57)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C_3)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf(d1_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X19 @ X18)
% 0.45/0.63          | ((X19) = (X16))
% 0.45/0.63          | ((X18) != (k1_tarski @ X16)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X16 : $i, X19 : $i]:
% 0.45/0.63         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      ((((sk_A) = (sk_C_3)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.63  thf('10', plain, ((((sk_A) != (sk_C_3))) <= (~ (((sk_A) = (sk_C_3))))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      ((((sk_A) != (sk_A)))
% 0.45/0.63         <= (~ (((sk_A) = (sk_C_3))) & 
% 0.45/0.63             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      ((((sk_A) = (sk_C_3))) | 
% 0.45/0.63       ~
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.63  thf('13', plain,
% 0.45/0.63      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('split', [status(esa)], ['3'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      ((((sk_A) = (sk_C_3)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D)))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('demod', [status(thm)], ['13', '14'])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.45/0.63         ((r2_hidden @ X56 @ X57)
% 0.45/0.63          | ~ (r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X57)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D))
% 0.45/0.63         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63               (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      ((~ (r2_hidden @ sk_B @ sk_D)) <= (~ ((r2_hidden @ sk_B @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.63       ~
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (~
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '12', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63          (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.45/0.63  thf('22', plain, ((((sk_A) = (sk_C_3))) <= ((((sk_A) = (sk_C_3))))),
% 0.45/0.63      inference('split', [status(esa)], ['3'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      ((((sk_A) = (sk_C_3))) | 
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['3'])).
% 0.45/0.63  thf('24', plain, ((((sk_A) = (sk_C_3)))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '12', '19', '23'])).
% 0.45/0.63  thf('25', plain, (((sk_A) = (sk_C_3))),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['22', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D))),
% 0.45/0.63      inference('demod', [status(thm)], ['21', '25'])).
% 0.45/0.63  thf(t70_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i]:
% 0.45/0.63         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.45/0.63      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.63  thf(t69_enumset1, axiom,
% 0.45/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf(d1_enumset1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.63           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_2, axiom,
% 0.45/0.63    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.63     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.63       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_3, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.63     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.63       ( ![E:$i]:
% 0.45/0.63         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.45/0.63          | (r2_hidden @ X9 @ X13)
% 0.45/0.63          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.63         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.45/0.63          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.45/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.45/0.63          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['29', '31'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.63         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.45/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.63  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['32', '34'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)
% 0.45/0.63        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63           (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['36'])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.45/0.63       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.45/0.63         (k2_zfmisc_1 @ (k1_tarski @ sk_C_3) @ sk_D)))),
% 0.45/0.63      inference('split', [status(esa)], ['36'])).
% 0.45/0.63  thf('39', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.45/0.63      inference('sat_resolution*', [status(thm)], ['2', '12', '19', '38'])).
% 0.45/0.63  thf('40', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.45/0.63      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X54 : $i, X55 : $i, X56 : $i, X58 : $i]:
% 0.45/0.63         ((r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X58))
% 0.45/0.63          | ~ (r2_hidden @ X56 @ X58)
% 0.45/0.63          | ~ (r2_hidden @ X54 @ X55))),
% 0.45/0.63      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X1 @ X0)
% 0.45/0.63          | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.45/0.63          (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '42'])).
% 0.45/0.63  thf('44', plain, ($false), inference('demod', [status(thm)], ['26', '43'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
