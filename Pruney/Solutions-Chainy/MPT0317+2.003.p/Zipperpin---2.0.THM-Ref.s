%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MSBZ7btVsz

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:19 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 157 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  503 (1677 expanded)
%              Number of equality atoms :   36 ( 108 expanded)
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

thf(t129_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
      <=> ( ( r2_hidden @ A @ C )
          & ( B = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t129_zfmisc_1])).

thf('0',plain,
    ( ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D )
    | ~ ( r2_hidden @ sk_A @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
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
    ( ( r2_hidden @ sk_A @ sk_C_3 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_3 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C_3 )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('10',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( r2_hidden @ X56 @ X57 )
      | ~ ( r2_hidden @ ( k4_tarski @ X54 @ X56 ) @ ( k2_zfmisc_1 @ X55 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('13',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B = sk_D )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','8','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('23',plain,(
    sk_B = sk_D ),
    inference('sat_resolution*',[status(thm)],['2','8','17','22'])).

thf('24',plain,(
    sk_B = sk_D ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_C_3 )
   <= ( r2_hidden @ sk_A @ sk_C_3 ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C_3 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['2','8','17','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_C_3 ),
    inference(simpl_trail,[status(thm)],['26','28'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

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

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X54: $i,X55: $i,X56: $i,X58: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X54 @ X56 ) @ ( k2_zfmisc_1 @ X55 @ X58 ) )
      | ~ ( r2_hidden @ X56 @ X58 )
      | ~ ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C_3 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['25','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MSBZ7btVsz
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 437 iterations in 0.186s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.64  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.64  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(t129_zfmisc_1, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( r2_hidden @
% 0.46/0.64         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.46/0.64       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64        ( ( r2_hidden @
% 0.46/0.64            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.46/0.64          ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t129_zfmisc_1])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((((sk_B) != (sk_D))
% 0.46/0.64        | ~ (r2_hidden @ sk_A @ sk_C_3)
% 0.46/0.64        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64             (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64           (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))
% 0.46/0.64         <= (~
% 0.46/0.64             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (~
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))) | 
% 0.46/0.64       ~ (((sk_B) = (sk_D))) | ~ ((r2_hidden @ sk_A @ sk_C_3))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_3)
% 0.46/0.64        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64           (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))
% 0.46/0.64         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf(t106_zfmisc_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.46/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.46/0.64         ((r2_hidden @ X54 @ X55)
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X57)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_3))
% 0.46/0.64         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((~ (r2_hidden @ sk_A @ sk_C_3)) <= (~ ((r2_hidden @ sk_A @ sk_C_3)))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_3)) | 
% 0.46/0.64       ~
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))
% 0.46/0.64         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.46/0.64         ((r2_hidden @ X56 @ X57)
% 0.46/0.64          | ~ (r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X57)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.46/0.64         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf(d1_tarski, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.46/0.64       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X19 @ X18)
% 0.46/0.64          | ((X19) = (X16))
% 0.46/0.64          | ((X18) != (k1_tarski @ X16)))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tarski])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X16 : $i, X19 : $i]:
% 0.46/0.64         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      ((((sk_B) = (sk_D)))
% 0.46/0.64         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '13'])).
% 0.46/0.64  thf('15', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.46/0.64      inference('split', [status(esa)], ['0'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      ((((sk_B) != (sk_B)))
% 0.46/0.64         <= (~ (((sk_B) = (sk_D))) & 
% 0.46/0.64             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64               (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      ((((sk_B) = (sk_D))) | 
% 0.46/0.64       ~
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (~
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['2', '8', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64          (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D)))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      ((((sk_B) = (sk_D))
% 0.46/0.64        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64           (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('21', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.46/0.64      inference('split', [status(esa)], ['20'])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((((sk_B) = (sk_D))) | 
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('split', [status(esa)], ['20'])).
% 0.46/0.64  thf('23', plain, ((((sk_B) = (sk_D)))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['2', '8', '17', '22'])).
% 0.46/0.64  thf('24', plain, (((sk_B) = (sk_D))),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64          (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_B)))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '24'])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_3)) <= (((r2_hidden @ sk_A @ sk_C_3)))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (((r2_hidden @ sk_A @ sk_C_3)) | 
% 0.46/0.64       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.46/0.64         (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ sk_D))))),
% 0.46/0.64      inference('split', [status(esa)], ['3'])).
% 0.46/0.64  thf('28', plain, (((r2_hidden @ sk_A @ sk_C_3))),
% 0.46/0.64      inference('sat_resolution*', [status(thm)], ['2', '8', '17', '27'])).
% 0.46/0.64  thf('29', plain, ((r2_hidden @ sk_A @ sk_C_3)),
% 0.46/0.64      inference('simpl_trail', [status(thm)], ['26', '28'])).
% 0.46/0.64  thf(t70_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X22 : $i, X23 : $i]:
% 0.46/0.64         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.46/0.64      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.46/0.64  thf(t69_enumset1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.46/0.64      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['30', '31'])).
% 0.46/0.64  thf(d1_enumset1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.64       ( ![E:$i]:
% 0.46/0.64         ( ( r2_hidden @ E @ D ) <=>
% 0.46/0.64           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.46/0.64  thf(zf_stmt_2, axiom,
% 0.46/0.64    (![E:$i,C:$i,B:$i,A:$i]:
% 0.46/0.64     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.46/0.64       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_3, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.46/0.64       ( ![E:$i]:
% 0.46/0.64         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.64         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.46/0.64          | (r2_hidden @ X9 @ X13)
% 0.46/0.64          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.46/0.64          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.46/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.46/0.64          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['32', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.64         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.46/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.46/0.64  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['35', '37'])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X54 : $i, X55 : $i, X56 : $i, X58 : $i]:
% 0.46/0.64         ((r2_hidden @ (k4_tarski @ X54 @ X56) @ (k2_zfmisc_1 @ X55 @ X58))
% 0.46/0.64          | ~ (r2_hidden @ X56 @ X58)
% 0.46/0.64          | ~ (r2_hidden @ X54 @ X55))),
% 0.46/0.64      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (~ (r2_hidden @ X2 @ X1)
% 0.46/0.64          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.46/0.64             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (r2_hidden @ (k4_tarski @ sk_A @ X0) @ 
% 0.46/0.64          (k2_zfmisc_1 @ sk_C_3 @ (k1_tarski @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['29', '40'])).
% 0.46/0.64  thf('42', plain, ($false), inference('demod', [status(thm)], ['25', '41'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
