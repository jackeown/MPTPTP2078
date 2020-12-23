%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vX752Nhk2I

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 131 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  704 (1502 expanded)
%              Number of equality atoms :   60 ( 144 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ( ( sk_B = sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B = sk_D ) ),
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

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ( X1 = X2 )
      | ( X1 = X3 )
      | ( X1 = X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ( ( sk_A = sk_C )
      | ( sk_A = sk_C )
      | ( sk_A = sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('20',plain,
    ( ~ ( zip_tseitin_0 @ sk_B @ sk_D @ sk_D @ sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_B = sk_D )
      | ( sk_B = sk_D )
      | ( sk_B = sk_D ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,
    ( ( sk_B = sk_D )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_B != sk_D )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != sk_D )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B = sk_D ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['23'])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ ( k2_zfmisc_1 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( sk_B = sk_D )
   <= ( sk_B = sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
      & ( sk_A = sk_C )
      & ( sk_B = sk_D ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('47',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['23'])).

thf('48',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ ( k1_tarski @ sk_D ) ) )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','44','45','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vX752Nhk2I
% 0.14/0.36  % Computer   : n002.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:38:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 83 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(t34_zfmisc_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @
% 0.22/0.50         ( k4_tarski @ A @ B ) @ 
% 0.22/0.50         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.50       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ( r2_hidden @
% 0.22/0.50            ( k4_tarski @ A @ B ) @ 
% 0.22/0.50            ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.22/0.50          ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t34_zfmisc_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((((sk_B) = (sk_D))
% 0.22/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       (((sk_B) = (sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf(d1_enumset1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, axiom,
% 0.22/0.50    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.22/0.50          | ((X1) = (X2))
% 0.22/0.50          | ((X1) = (X3))
% 0.22/0.50          | ((X1) = (X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((((sk_A) = (sk_C))
% 0.22/0.50        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 0.22/0.50          | ((X1) = (X2))
% 0.22/0.50          | ((X1) = (X3))
% 0.22/0.50          | ((X1) = (X4)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf(l54_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((r2_hidden @ X13 @ X14)
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf(t76_enumset1, axiom,
% 0.22/0.50    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X12 : $i]: ((k1_enumset1 @ X12 @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.22/0.50  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X10 @ X9)
% 0.22/0.50          | ~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.22/0.50          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.22/0.50         (~ (zip_tseitin_0 @ X10 @ X6 @ X7 @ X8)
% 0.22/0.50          | ~ (r2_hidden @ X10 @ (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((~ (zip_tseitin_0 @ sk_A @ sk_C @ sk_C @ sk_C))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (((((sk_A) = (sk_C)) | ((sk_A) = (sk_C)) | ((sk_A) = (sk_C))))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((((sk_A) = (sk_C)))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('demod', [status(thm)], ['4', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((r2_hidden @ X15 @ X16)
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X16)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D)))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '11'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((~ (zip_tseitin_0 @ sk_B @ sk_D @ sk_D @ sk_D))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((((sk_B) = (sk_D)) | ((sk_B) = (sk_D)) | ((sk_B) = (sk_D))))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((((sk_B) = (sk_D)))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((((sk_B) != (sk_D))
% 0.22/0.50        | ((sk_A) != (sk_C))
% 0.22/0.50        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((((sk_B) != (sk_B)))
% 0.22/0.50         <= (~ (((sk_B) = (sk_D))) & 
% 0.22/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (~
% 0.22/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       (((sk_B) = (sk_D)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (~ (((sk_A) = (sk_C))) | 
% 0.22/0.50       ~
% 0.22/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       ~ (((sk_B) = (sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['23'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X12 : $i]: ((k1_enumset1 @ X12 @ X12 @ X12) = (k1_tarski @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.22/0.50          | (r2_hidden @ X5 @ X9)
% 0.22/0.50          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.50         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.22/0.50          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.22/0.50      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.50          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.22/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.50  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.50  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '33'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.22/0.50         ((r2_hidden @ (k4_tarski @ X13 @ X15) @ (k2_zfmisc_1 @ X14 @ X17))
% 0.22/0.50          | ~ (r2_hidden @ X15 @ X17)
% 0.22/0.50          | ~ (r2_hidden @ X13 @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ X1)
% 0.22/0.50          | (r2_hidden @ (k4_tarski @ X2 @ X0) @ 
% 0.22/0.50             (k2_zfmisc_1 @ X1 @ (k1_tarski @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (r2_hidden @ (k4_tarski @ X0 @ X1) @ 
% 0.22/0.50          (k2_zfmisc_1 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.50  thf('39', plain, ((((sk_B) = (sk_D))) <= ((((sk_B) = (sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('40', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D))))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('split', [status(esa)], ['23'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.22/0.50             (((sk_A) = (sk_C))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) & 
% 0.22/0.50             (((sk_A) = (sk_C))) & 
% 0.22/0.50             (((sk_B) = (sk_D))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       ~ (((sk_A) = (sk_C))) | ~ (((sk_B) = (sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '43'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       (((sk_A) = (sk_C)))),
% 0.22/0.50      inference('split', [status(esa)], ['3'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((((sk_A) = (sk_C)))
% 0.22/0.50         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.22/0.50  thf('47', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['23'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      ((((sk_A) != (sk_A)))
% 0.22/0.50         <= (~ (((sk_A) = (sk_C))) & 
% 0.22/0.50             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (~
% 0.22/0.50       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.22/0.50         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ (k1_tarski @ sk_D)))) | 
% 0.22/0.50       (((sk_A) = (sk_C)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.22/0.50  thf('50', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)],
% 0.22/0.50                ['1', '26', '27', '44', '45', '49'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
