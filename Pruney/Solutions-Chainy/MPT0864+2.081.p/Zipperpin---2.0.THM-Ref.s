%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFySSd2yV1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  99 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  421 ( 774 expanded)
%              Number of equality atoms :   66 ( 131 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
      = ( k1_tarski @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) )
      | ( X33
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( r1_tarski @ ( k1_tarski @ X29 ) @ ( k1_enumset1 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,
    ( $false
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('26',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X35 ) )
      = ( k1_tarski @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('34',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['24','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aFySSd2yV1
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:02:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 87 iterations in 0.030s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.49  thf(t20_mcart_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.49       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.49          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.22/0.49  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t7_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.22/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.49  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('5', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['2', '4'])).
% 0.22/0.49  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.22/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(t35_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.22/0.49       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X34 : $i, X35 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.22/0.49           = (k1_tarski @ (k4_tarski @ X34 @ X35)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.49  thf(t135_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.22/0.49         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.49       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         (((X27) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X27 @ (k2_zfmisc_1 @ X28 @ X27)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.49          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(t69_enumset1, axiom,
% 0.22/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.49  thf('11', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t41_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_tarski @ A @ B ) =
% 0.22/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((k2_tarski @ X2 @ X3)
% 0.22/0.49           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.22/0.49  thf(t49_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X36 : $i, X37 : $i]:
% 0.22/0.49         ((k2_xboole_0 @ (k1_tarski @ X36) @ X37) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.49  thf('15', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['10', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '16'])).
% 0.22/0.49  thf('18', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.49  thf(t70_enumset1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.49  thf(t142_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.49       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.22/0.49            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.22/0.49            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.22/0.49            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.22/0.49            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.22/0.49            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X29 : $i, X30 : $i, X31 : $i, X33 : $i]:
% 0.22/0.49         ((r1_tarski @ X33 @ (k1_enumset1 @ X29 @ X30 @ X31))
% 0.22/0.49          | ((X33) != (k1_tarski @ X29)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.49         (r1_tarski @ (k1_tarski @ X29) @ (k1_enumset1 @ X29 @ X30 @ X31))),
% 0.22/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['19', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['18', '22'])).
% 0.22/0.49  thf('24', plain, (($false) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['18', '22'])).
% 0.22/0.49  thf('26', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.22/0.49  thf('28', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.22/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('30', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.22/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X34 : $i, X35 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k1_tarski @ X34) @ (k1_tarski @ X35))
% 0.22/0.49           = (k1_tarski @ (k4_tarski @ X34 @ X35)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X27 : $i, X28 : $i]:
% 0.22/0.49         (((X27) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X27 @ (k2_zfmisc_1 @ X27 @ X28)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.49          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))
% 0.22/0.49         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['32', '37'])).
% 0.22/0.49  thf('39', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '38'])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('41', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain, ($false),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['24', '41'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
