%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLEvWmS3XT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:22 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :  401 ( 702 expanded)
%              Number of equality atoms :   65 ( 109 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X27 @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
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

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('19',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X27 @ X26 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_A_1 = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_A_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','22'])).

thf('34',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( k2_zfmisc_1 @ sk_A_1 @ ( k1_tarski @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['24','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NLEvWmS3XT
% 0.15/0.37  % Computer   : n007.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:57:51 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 210 iterations in 0.108s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.60  thf(t130_zfmisc_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i]:
% 0.42/0.60        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.42/0.60          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.60            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))
% 0.42/0.60        | ((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf(t113_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i]:
% 0.42/0.60         (((X26) = (k1_xboole_0))
% 0.42/0.60          | ((X27) = (k1_xboole_0))
% 0.42/0.60          | ((k2_zfmisc_1 @ X27 @ X26) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.60         | ((sk_A_1) = (k1_xboole_0))
% 0.42/0.60         | ((k1_tarski @ sk_B_1) = (k1_xboole_0))))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (((((k1_tarski @ sk_B_1) = (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0))))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['3'])).
% 0.42/0.60  thf('5', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf(t69_enumset1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.60  thf('7', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.42/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.60  thf(t70_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X17 : $i, X18 : $i]:
% 0.42/0.60         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.42/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.60  thf(d1_enumset1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.60       ( ![E:$i]:
% 0.42/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_2, axiom,
% 0.42/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_3, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.60       ( ![E:$i]:
% 0.42/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.60         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.42/0.60          | (r2_hidden @ X9 @ X13)
% 0.42/0.60          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.42/0.60          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.42/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.42/0.60          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.42/0.60      inference('sup+', [status(thm)], ['8', '10'])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.60         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.42/0.60      inference('simplify', [status(thm)], ['12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '13'])).
% 0.42/0.60  thf(d1_xboole_0, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.60  thf('17', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '16'])).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['6', '17'])).
% 0.42/0.60  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.42/0.60  thf('19', plain, ((v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.42/0.60  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.42/0.60  thf(l13_xboole_0, axiom,
% 0.42/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.60  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.60  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (($false)
% 0.42/0.60         <= ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))))),
% 0.42/0.60      inference('demod', [status(thm)], ['18', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X26 : $i, X27 : $i]:
% 0.42/0.60         (((X26) = (k1_xboole_0))
% 0.42/0.60          | ((X27) = (k1_xboole_0))
% 0.42/0.60          | ((k2_zfmisc_1 @ X27 @ X26) != (k1_xboole_0)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.60         | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.42/0.60         | ((sk_A_1) = (k1_xboole_0))))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (((((sk_A_1) = (k1_xboole_0)) | ((k1_tarski @ sk_B_1) = (k1_xboole_0))))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.42/0.60  thf('29', plain, (((sk_A_1) != (k1_xboole_0))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.42/0.60      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.42/0.60  thf('31', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '16'])).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.42/0.60         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0))) | 
% 0.42/0.60       (((k2_zfmisc_1 @ (k1_tarski @ sk_B_1) @ sk_A_1) = (k1_xboole_0)))),
% 0.42/0.60      inference('split', [status(esa)], ['0'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      ((((k2_zfmisc_1 @ sk_A_1 @ (k1_tarski @ sk_B_1)) = (k1_xboole_0)))),
% 0.42/0.60      inference('sat_resolution*', [status(thm)], ['34', '35'])).
% 0.42/0.60  thf('37', plain, ($false),
% 0.42/0.60      inference('simpl_trail', [status(thm)], ['24', '36'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
