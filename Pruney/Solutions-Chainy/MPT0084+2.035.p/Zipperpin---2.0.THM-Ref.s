%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hHdPVJIVxQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:23 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   58 (  84 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  472 ( 845 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
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

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ X1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hHdPVJIVxQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 1397 iterations in 0.593s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.83/1.04  thf(t77_xboole_1, conjecture,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.83/1.04          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.83/1.04        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.83/1.04             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.83/1.04  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t3_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.83/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.83/1.04            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('3', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t28_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.83/1.04  thf('4', plain,
% 0.83/1.04      (![X10 : $i, X11 : $i]:
% 0.83/1.04         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.83/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.83/1.04  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) = (sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['3', '4'])).
% 0.83/1.04  thf(d4_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.83/1.04       ( ![D:$i]:
% 0.83/1.04         ( ( r2_hidden @ D @ C ) <=>
% 0.83/1.04           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X4 @ X3)
% 0.83/1.04          | (r2_hidden @ X4 @ X2)
% 0.83/1.04          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.83/1.04         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['6'])).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_C_1))),
% 0.83/1.04      inference('sup-', [status(thm)], ['5', '7'])).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.83/1.04      inference('sup-', [status(thm)], ['2', '8'])).
% 0.83/1.04  thf('10', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X0 @ X1)
% 0.83/1.04          | ~ (r2_hidden @ X0 @ X2)
% 0.83/1.04          | (r2_hidden @ X0 @ X3)
% 0.83/1.04          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.83/1.04  thf('11', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.83/1.04          | ~ (r2_hidden @ X0 @ X2)
% 0.83/1.04          | ~ (r2_hidden @ X0 @ X1))),
% 0.83/1.04      inference('simplify', [status(thm)], ['10'])).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ sk_A @ X0)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ X1)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ X1 @ sk_C_1)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['9', '11'])).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ sk_A @ X0)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_1))
% 0.83/1.04          | (r1_xboole_0 @ sk_A @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['1', '12'])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_C_1))
% 0.83/1.04          | (r1_xboole_0 @ sk_A @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['13'])).
% 0.83/1.04  thf('15', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X8 @ X6)
% 0.83/1.04          | ~ (r2_hidden @ X8 @ X9)
% 0.83/1.04          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X1 @ X0)
% 0.83/1.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.04  thf('20', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.83/1.04          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.83/1.04          | (r1_xboole_0 @ X0 @ X1))),
% 0.83/1.04      inference('sup-', [status(thm)], ['16', '19'])).
% 0.83/1.04  thf('21', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.83/1.04      inference('simplify', [status(thm)], ['20'])).
% 0.83/1.04  thf('22', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.83/1.04      inference('sup-', [status(thm)], ['15', '21'])).
% 0.83/1.04  thf('23', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('24', plain,
% 0.83/1.04      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.83/1.04         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['6'])).
% 0.83/1.04  thf('25', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['23', '24'])).
% 0.83/1.04  thf('26', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X1 @ X0)
% 0.83/1.04          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.04  thf('27', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.04          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.83/1.04          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['25', '26'])).
% 0.83/1.04  thf('28', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         (~ (r1_xboole_0 @ X2 @ X0)
% 0.83/1.04          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.83/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.83/1.04  thf('29', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ 
% 0.83/1.04          (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.83/1.04      inference('sup-', [status(thm)], ['22', '28'])).
% 0.83/1.04  thf('30', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('31', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('32', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.83/1.04          | ~ (r2_hidden @ X0 @ X2)
% 0.83/1.04          | ~ (r2_hidden @ X0 @ X1))),
% 0.83/1.04      inference('simplify', [status(thm)], ['10'])).
% 0.83/1.04  thf('33', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.04  thf('34', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X1 @ X0)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.83/1.04          | (r1_xboole_0 @ X1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['30', '33'])).
% 0.83/1.04  thf('35', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 0.83/1.04          | (r1_xboole_0 @ X1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['34'])).
% 0.83/1.04  thf('36', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['31', '32'])).
% 0.83/1.04  thf('37', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.83/1.04          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.83/1.04             (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.83/1.04          | (r1_xboole_0 @ X0 @ X1))),
% 0.83/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.83/1.04  thf('38', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         ((r2_hidden @ (sk_C @ X1 @ X0) @ 
% 0.83/1.04           (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))
% 0.83/1.04          | (r1_xboole_0 @ X0 @ X1))),
% 0.83/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.83/1.04  thf('39', plain,
% 0.83/1.04      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X8 @ X6)
% 0.83/1.04          | ~ (r2_hidden @ X8 @ X9)
% 0.83/1.04          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.83/1.04  thf('40', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X0 @ X1)
% 0.83/1.04          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) @ X2)
% 0.83/1.04          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.83/1.04      inference('sup-', [status(thm)], ['38', '39'])).
% 0.83/1.04  thf('41', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 0.83/1.04          | (r1_xboole_0 @ sk_A @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['29', '40'])).
% 0.83/1.04  thf('42', plain,
% 0.83/1.04      (((r1_xboole_0 @ sk_A @ sk_B) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['14', '41'])).
% 0.83/1.04  thf('43', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.83/1.04      inference('simplify', [status(thm)], ['42'])).
% 0.83/1.04  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
