%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3JeoBbOuTh

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 112 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  486 (1032 expanded)
%              Number of equality atoms :   81 ( 188 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X35 @ X34 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('8',plain,(
    ! [X37: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('9',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('10',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X42: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X39 @ X40 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X42 ) ) )
      | ( X40 != X42 )
      | ( X39 != X38 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('14',plain,(
    ! [X38: $i,X42: $i] :
      ( r2_hidden @ ( k4_tarski @ X38 @ X42 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_zfmisc_1 @ X35 @ X36 )
        = k1_xboole_0 )
      | ( X35 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X36 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X35 @ X34 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('26',plain,(
    ! [X37: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('27',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X38: $i,X42: $i] :
      ( r2_hidden @ ( k4_tarski @ X38 @ X42 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X36: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X36 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('39',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['18','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3JeoBbOuTh
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:33 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 65 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t130_zfmisc_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf(t113_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         (((X34) = (k1_xboole_0))
% 0.20/0.49          | ((X35) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X35 @ X34) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49         | ((sk_A) = (k1_xboole_0))
% 0.20/0.49         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(t31_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.49  thf('8', plain, (![X37 : $i]: ((k3_tarski @ (k1_tarski @ X37)) = (X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.49  thf('10', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '11'])).
% 0.20/0.49  thf(t34_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @
% 0.20/0.49         ( k4_tarski @ A @ B ) @ 
% 0.20/0.49         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.20/0.49       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i, X42 : $i]:
% 0.20/0.49         ((r2_hidden @ (k4_tarski @ X39 @ X40) @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_tarski @ X38) @ (k1_tarski @ X42)))
% 0.20/0.49          | ((X40) != (X42))
% 0.20/0.49          | ((X39) != (X38)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X38 : $i, X42 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ X38 @ X42) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ X38) @ (k1_tarski @ X42)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (r2_hidden @ (k4_tarski @ k1_xboole_0 @ X0) @ 
% 0.20/0.49           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i]:
% 0.20/0.49         (((k2_zfmisc_1 @ X35 @ X36) = (k1_xboole_0))
% 0.20/0.49          | ((X35) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X36 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X36) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ k1_xboole_0 @ X0) @ k1_xboole_0))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         (((X34) = (k1_xboole_0))
% 0.20/0.49          | ((X35) = (k1_xboole_0))
% 0.20/0.49          | ((k2_zfmisc_1 @ X35 @ X34) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.20/0.49         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.49  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('26', plain, (![X37 : $i]: ((k3_tarski @ (k1_tarski @ X37)) = (X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X38 : $i, X42 : $i]:
% 0.20/0.49         (r2_hidden @ (k4_tarski @ X38 @ X42) @ 
% 0.20/0.49          (k2_zfmisc_1 @ (k1_tarski @ X38) @ (k1_tarski @ X42)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((![X0 : $i]:
% 0.20/0.49          (r2_hidden @ (k4_tarski @ k1_xboole_0 @ X0) @ 
% 0.20/0.49           (k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X36 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X36) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((![X0 : $i]: (r2_hidden @ (k4_tarski @ k1_xboole_0 @ X0) @ k1_xboole_0))
% 0.20/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf(t4_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.49  thf('38', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.49  thf('39', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.20/0.49       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]: (r2_hidden @ (k4_tarski @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['18', '42'])).
% 0.20/0.49  thf('44', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('45', plain, ($false), inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
