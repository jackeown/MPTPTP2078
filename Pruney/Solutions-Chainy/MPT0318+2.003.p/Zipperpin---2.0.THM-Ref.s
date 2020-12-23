%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PjTEdBdW6I

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:21 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 131 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (1061 expanded)
%              Number of equality atoms :   80 ( 188 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ( X42
       != ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r2_hidden @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','6'])).

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

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X46 @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('16',plain,(
    ! [X48: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('17',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('18',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('22',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X46 @ X45 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X48: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('29',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf('34',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
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
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','41'])).

thf('43',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('45',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['20','45'])).

thf('47',plain,(
    r2_hidden @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','41'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PjTEdBdW6I
% 0.17/0.39  % Computer   : n007.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 17:22:06 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.49  % Solved by: fo/fo7.sh
% 0.25/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.49  % done 79 iterations in 0.017s
% 0.25/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.49  % SZS output start Refutation
% 0.25/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.25/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.25/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.49  thf(t1_zfmisc_1, axiom,
% 0.25/0.49    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.25/0.49  thf('0', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.25/0.49  thf(t2_boole, axiom,
% 0.25/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.25/0.49  thf('1', plain,
% 0.25/0.49      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.25/0.49  thf(t17_xboole_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.25/0.49  thf('2', plain,
% 0.25/0.49      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.25/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.25/0.49  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.25/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.25/0.49  thf(d1_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.25/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.25/0.49  thf('4', plain,
% 0.25/0.49      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.25/0.49         (~ (r1_tarski @ X40 @ X41)
% 0.25/0.49          | (r2_hidden @ X40 @ X42)
% 0.25/0.49          | ((X42) != (k1_zfmisc_1 @ X41)))),
% 0.25/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.25/0.49  thf('5', plain,
% 0.25/0.49      (![X40 : $i, X41 : $i]:
% 0.25/0.49         ((r2_hidden @ X40 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X40 @ X41))),
% 0.25/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.25/0.49  thf('6', plain, (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.25/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.25/0.49  thf('7', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.25/0.49      inference('sup+', [status(thm)], ['0', '6'])).
% 0.25/0.49  thf(t130_zfmisc_1, conjecture,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.25/0.49       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.49         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.25/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.49    (~( ![A:$i,B:$i]:
% 0.25/0.49        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.25/0.49          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.49            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.25/0.49    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.25/0.49  thf('8', plain,
% 0.25/0.49      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.25/0.49        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('9', plain,
% 0.25/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('split', [status(esa)], ['8'])).
% 0.25/0.49  thf(t113_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.25/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.25/0.49  thf('10', plain,
% 0.25/0.49      (![X45 : $i, X46 : $i]:
% 0.25/0.49         (((X45) = (k1_xboole_0))
% 0.25/0.49          | ((X46) = (k1_xboole_0))
% 0.25/0.49          | ((k2_zfmisc_1 @ X46 @ X45) != (k1_xboole_0)))),
% 0.25/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.49  thf('11', plain,
% 0.25/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.49         | ((sk_A) = (k1_xboole_0))
% 0.25/0.49         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.49  thf('12', plain,
% 0.25/0.49      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.25/0.49  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('14', plain,
% 0.25/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.25/0.49  thf('15', plain,
% 0.25/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.25/0.49  thf(t31_zfmisc_1, axiom,
% 0.25/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.25/0.49  thf('16', plain, (![X48 : $i]: ((k3_tarski @ (k1_tarski @ X48)) = (X48))),
% 0.25/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.25/0.49  thf('17', plain,
% 0.25/0.49      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.25/0.49  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.25/0.49  thf('18', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.25/0.49  thf('19', plain,
% 0.25/0.49      ((((sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup+', [status(thm)], ['17', '18'])).
% 0.25/0.49  thf('20', plain,
% 0.25/0.49      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.25/0.49      inference('demod', [status(thm)], ['14', '19'])).
% 0.25/0.49  thf('21', plain,
% 0.25/0.49      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('split', [status(esa)], ['8'])).
% 0.25/0.49  thf('22', plain,
% 0.25/0.49      (![X45 : $i, X46 : $i]:
% 0.25/0.49         (((X45) = (k1_xboole_0))
% 0.25/0.49          | ((X46) = (k1_xboole_0))
% 0.25/0.49          | ((k2_zfmisc_1 @ X46 @ X45) != (k1_xboole_0)))),
% 0.25/0.49      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.25/0.49  thf('23', plain,
% 0.25/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.49         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.25/0.49         | ((sk_A) = (k1_xboole_0))))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.49  thf('24', plain,
% 0.25/0.49      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.25/0.49  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.49  thf('26', plain,
% 0.25/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.25/0.49  thf('27', plain,
% 0.25/0.49      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.25/0.49  thf('28', plain, (![X48 : $i]: ((k3_tarski @ (k1_tarski @ X48)) = (X48))),
% 0.25/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.25/0.49  thf('29', plain,
% 0.25/0.49      ((((k3_tarski @ k1_xboole_0) = (sk_B)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.25/0.49  thf('30', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.25/0.49  thf('31', plain,
% 0.25/0.49      ((((sk_B) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup+', [status(thm)], ['29', '30'])).
% 0.25/0.49  thf('32', plain,
% 0.25/0.49      ((((k1_tarski @ k1_xboole_0) = (k1_xboole_0)))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('demod', [status(thm)], ['26', '31'])).
% 0.25/0.49  thf('33', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 0.25/0.49      inference('sup+', [status(thm)], ['0', '6'])).
% 0.25/0.49  thf('34', plain,
% 0.25/0.49      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0))
% 0.25/0.49         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.25/0.49      inference('sup+', [status(thm)], ['32', '33'])).
% 0.25/0.49  thf('35', plain,
% 0.25/0.49      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.25/0.49  thf(t4_xboole_0, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.25/0.49  thf('36', plain,
% 0.25/0.49      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.25/0.49         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.25/0.49          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.25/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.25/0.49  thf('37', plain,
% 0.25/0.49      (![X0 : $i, X1 : $i]:
% 0.25/0.49         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.25/0.49  thf('38', plain,
% 0.25/0.49      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.25/0.49  thf(d7_xboole_0, axiom,
% 0.25/0.49    (![A:$i,B:$i]:
% 0.25/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.25/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.49  thf('39', plain,
% 0.25/0.49      (![X2 : $i, X4 : $i]:
% 0.25/0.49         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.25/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.49  thf('40', plain,
% 0.25/0.49      (![X0 : $i]:
% 0.25/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.25/0.49  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.25/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.25/0.49  thf('42', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.25/0.49      inference('demod', [status(thm)], ['37', '41'])).
% 0.25/0.49  thf('43', plain,
% 0.25/0.49      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.25/0.49      inference('sup-', [status(thm)], ['34', '42'])).
% 0.25/0.49  thf('44', plain,
% 0.25/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.25/0.49       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.25/0.49      inference('split', [status(esa)], ['8'])).
% 0.25/0.49  thf('45', plain,
% 0.25/0.49      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.25/0.49      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.25/0.49  thf('46', plain, (((k1_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.49      inference('simpl_trail', [status(thm)], ['20', '45'])).
% 0.25/0.49  thf('47', plain, ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.25/0.49      inference('demod', [status(thm)], ['7', '46'])).
% 0.25/0.49  thf('48', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.25/0.49      inference('demod', [status(thm)], ['37', '41'])).
% 0.25/0.49  thf('49', plain, ($false), inference('sup-', [status(thm)], ['47', '48'])).
% 0.25/0.49  
% 0.25/0.49  % SZS output end Refutation
% 0.25/0.49  
% 0.25/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
