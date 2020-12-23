%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tvO7YTp4uk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 130 expanded)
%              Number of leaves         :   17 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  388 (1080 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ B ) )
        & ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ C @ B ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ B ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ C @ B ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X21: $i] :
      ( ( r1_xboole_0 @ X21 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('16',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('20',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['15'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['13','33'])).

thf('35',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['4','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X20 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_B ) @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('44',plain,(
    sk_A = sk_C_2 ),
    inference(demod,[status(thm)],['37','42','43'])).

thf('45',plain,(
    sk_A != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tvO7YTp4uk
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:42:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 117 iterations in 0.052s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(t71_xboole_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.19/0.50         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.50       ( ( A ) = ( C ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.50        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.19/0.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.19/0.50          ( ( A ) = ( C ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (((k2_xboole_0 @ sk_A @ sk_B) = (k2_xboole_0 @ sk_C_2 @ sk_B))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t40_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.19/0.50           = (k4_xboole_0 @ X15 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B)
% 0.19/0.50         = (k4_xboole_0 @ sk_C_2 @ sk_B))),
% 0.19/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X15 : $i, X16 : $i]:
% 0.19/0.50         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.19/0.50           = (k4_xboole_0 @ X15 @ X16))),
% 0.19/0.50      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_C_2 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('5', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t3_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf(t4_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.19/0.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.50  thf(t66_xboole_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.19/0.50       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf(t51_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.19/0.50       ( A ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.19/0.50           = (X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.19/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X2 : $i, X3 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X21 : $i]: ((r1_xboole_0 @ X21 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('16', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.19/0.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.19/0.50          | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.50  thf('23', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.50  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['14', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.19/0.50           = (X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf(t39_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 0.19/0.50           = (k2_xboole_0 @ X13 @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.19/0.50  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('34', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '33'])).
% 0.19/0.50  thf('35', plain, (((sk_A) = (k4_xboole_0 @ sk_C_2 @ sk_B))),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i]:
% 0.19/0.50         ((k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k4_xboole_0 @ X19 @ X20))
% 0.19/0.50           = (X19))),
% 0.19/0.50      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (((k2_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_B) @ sk_A) = (sk_C_2))),
% 0.19/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.19/0.50          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_B) @ X0)),
% 0.19/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.19/0.50  thf('42', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf('44', plain, (((sk_A) = (sk_C_2))),
% 0.19/0.50      inference('demod', [status(thm)], ['37', '42', '43'])).
% 0.19/0.50  thf('45', plain, (((sk_A) != (sk_C_2))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('46', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
