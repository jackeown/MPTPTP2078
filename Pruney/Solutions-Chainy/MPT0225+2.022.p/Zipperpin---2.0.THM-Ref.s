%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gGYdbzHbg6

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 132 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  463 (1070 expanded)
%              Number of equality atoms :   68 ( 167 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
      | ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('13',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('29',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','34','35'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','36'])).

thf('38',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','37'])).

thf('39',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( X24 = X21 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('41',plain,(
    ! [X21: $i,X24: $i] :
      ( ( X24 = X21 )
      | ~ ( r2_hidden @ X24 @ ( k1_tarski @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['16','34'])).

thf('45',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gGYdbzHbg6
% 0.14/0.36  % Computer   : n012.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 15:21:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 114 iterations in 0.052s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(l27_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X34 : $i, X35 : $i]:
% 0.35/0.53         ((r1_xboole_0 @ (k1_tarski @ X34) @ X35) | (r2_hidden @ X34 @ X35))),
% 0.35/0.53      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.35/0.53  thf(d7_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.35/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ X1 @ X0)
% 0.35/0.53          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(t100_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X3 @ X4)
% 0.35/0.53           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.35/0.53            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ X1 @ X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.53  thf('5', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X3 @ X4)
% 0.35/0.53           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf(t3_boole, axiom,
% 0.35/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.35/0.53  thf('10', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.35/0.53  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.35/0.53          | (r2_hidden @ X1 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['4', '11'])).
% 0.35/0.53  thf(t20_zfmisc_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.53         ( k1_tarski @ A ) ) <=>
% 0.35/0.53       ( ( A ) != ( B ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.35/0.53            ( k1_tarski @ A ) ) <=>
% 0.35/0.53          ( ( A ) != ( B ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      ((((sk_A) = (sk_B))
% 0.35/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53            != (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          != (k1_tarski @ sk_A)))
% 0.35/0.53         <= (~
% 0.35/0.53             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))))),
% 0.35/0.53      inference('split', [status(esa)], ['13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((((sk_A) != (sk_B))
% 0.35/0.53        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53            = (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (~ (((sk_A) = (sk_B))) | 
% 0.35/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('split', [status(esa)], ['15'])).
% 0.35/0.53  thf('17', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.35/0.53  thf(t48_xboole_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]:
% 0.35/0.53         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.35/0.53           = (k3_xboole_0 @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.35/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['13'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A)))
% 0.35/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))))),
% 0.35/0.53      inference('split', [status(esa)], ['15'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A)))
% 0.35/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))) & 
% 0.35/0.53             (((sk_A) = (sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.35/0.53  thf('25', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['13'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_B)))
% 0.35/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))) & 
% 0.35/0.53             (((sk_A) = (sk_B))))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((((k1_xboole_0) = (k1_tarski @ sk_B)))
% 0.35/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))) & 
% 0.35/0.53             (((sk_A) = (sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['21', '26'])).
% 0.35/0.53  thf(d1_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.53         (((X22) != (X21))
% 0.35/0.53          | (r2_hidden @ X22 @ X23)
% 0.35/0.53          | ((X23) != (k1_tarski @ X21)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.53  thf('29', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.35/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (((r2_hidden @ sk_B @ k1_xboole_0))
% 0.35/0.53         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53                = (k1_tarski @ sk_A))) & 
% 0.35/0.53             (((sk_A) = (sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['27', '29'])).
% 0.35/0.53  thf('31', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.53  thf(l24_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X32 : $i, X33 : $i]:
% 0.35/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X32) @ X33) | ~ (r2_hidden @ X32 @ X33))),
% 0.35/0.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.35/0.53  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (~
% 0.35/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A))) | 
% 0.35/0.53       ~ (((sk_A) = (sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['30', '33'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (~
% 0.35/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A))) | 
% 0.35/0.53       (((sk_A) = (sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['13'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      (~
% 0.35/0.53       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53          = (k1_tarski @ sk_A)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['16', '34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.35/0.53         != (k1_tarski @ sk_A))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['14', '36'])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '37'])).
% 0.35/0.53  thf('39', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.35/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X24 @ X23)
% 0.35/0.53          | ((X24) = (X21))
% 0.35/0.53          | ((X23) != (k1_tarski @ X21)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      (![X21 : $i, X24 : $i]:
% 0.35/0.53         (((X24) = (X21)) | ~ (r2_hidden @ X24 @ (k1_tarski @ X21)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.35/0.53  thf('42', plain, (((sk_A) = (sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['39', '41'])).
% 0.35/0.53  thf('43', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['15'])).
% 0.35/0.53  thf('44', plain, (~ (((sk_A) = (sk_B)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['16', '34'])).
% 0.35/0.53  thf('45', plain, (((sk_A) != (sk_B))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.35/0.53  thf('46', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['42', '45'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
