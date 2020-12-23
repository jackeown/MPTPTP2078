%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMsUbMrquk

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:39 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   64 (  82 expanded)
%              Number of leaves         :   14 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 ( 628 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('4',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t1_mcart_1,conjecture,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( r2_hidden @ B @ A )
                & ( r1_xboole_0 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_mcart_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_A )
      | ~ ( r1_xboole_0 @ X13 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( sk_C_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( sk_C_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( sk_C_1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['30','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMsUbMrquk
% 0.16/0.38  % Computer   : n020.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 47 iterations in 0.020s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.25/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.25/0.51  thf(t3_boole, axiom,
% 0.25/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.25/0.51  thf('0', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.51  thf(t48_xboole_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.25/0.51  thf('1', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i]:
% 0.25/0.51         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.25/0.51           = (k3_xboole_0 @ X8 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['0', '1'])).
% 0.25/0.51  thf('3', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.51  thf('4', plain,
% 0.25/0.51      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.25/0.51  thf(d7_xboole_0, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.25/0.51       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X0 : $i, X2 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.25/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.51        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.51  thf('7', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.25/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.25/0.51  thf(t3_xboole_0, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.25/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.25/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.25/0.51            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X5 @ X3)
% 0.25/0.51          | ~ (r2_hidden @ X5 @ X6)
% 0.25/0.51          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('11', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.25/0.51          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.25/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.51          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.25/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.25/0.51  thf('13', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.25/0.51  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.25/0.51      inference('sup-', [status(thm)], ['7', '13'])).
% 0.25/0.51  thf('15', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('16', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('17', plain,
% 0.25/0.51      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X5 @ X3)
% 0.25/0.51          | ~ (r2_hidden @ X5 @ X6)
% 0.25/0.51          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('18', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X1 @ X0)
% 0.25/0.51          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.25/0.51          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.25/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.25/0.51  thf('19', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.25/0.51          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.25/0.51          | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('sup-', [status(thm)], ['15', '18'])).
% 0.25/0.51  thf('20', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.25/0.51  thf('21', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.25/0.51      inference('sup-', [status(thm)], ['14', '20'])).
% 0.25/0.51  thf('22', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.51  thf('23', plain,
% 0.25/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.51  thf('24', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i]:
% 0.25/0.51         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.25/0.51           = (k3_xboole_0 @ X8 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.51  thf('25', plain,
% 0.25/0.51      (![X8 : $i, X9 : $i]:
% 0.25/0.51         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.25/0.51           = (k3_xboole_0 @ X8 @ X9))),
% 0.25/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.25/0.51  thf('26', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.25/0.51           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.25/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.25/0.51  thf('27', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.25/0.51           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.25/0.51      inference('sup+', [status(thm)], ['23', '26'])).
% 0.25/0.51  thf('28', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.51  thf('29', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.25/0.51  thf('30', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.25/0.51      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.25/0.51  thf('31', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf(t7_tarski, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ~( ( r2_hidden @ A @ B ) & 
% 0.25/0.51          ( ![C:$i]:
% 0.25/0.51            ( ~( ( r2_hidden @ C @ B ) & 
% 0.25/0.51                 ( ![D:$i]:
% 0.25/0.51                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.25/0.51  thf('32', plain,
% 0.25/0.51      (![X10 : $i, X11 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11) @ X11))),
% 0.25/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.25/0.51  thf('33', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.25/0.51  thf(t1_mcart_1, conjecture,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i]:
% 0.25/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.25/0.51             ( ![B:$i]:
% 0.25/0.51               ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t1_mcart_1])).
% 0.25/0.51  thf('34', plain,
% 0.25/0.51      (![X13 : $i]: (~ (r2_hidden @ X13 @ sk_A) | ~ (r1_xboole_0 @ X13 @ sk_A))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('35', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.25/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.25/0.51  thf('36', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('37', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.25/0.51  thf('38', plain,
% 0.25/0.51      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X10 @ X11)
% 0.25/0.51          | ~ (r2_hidden @ X12 @ X11)
% 0.25/0.51          | ~ (r2_hidden @ X12 @ (sk_C_1 @ X11)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t7_tarski])).
% 0.25/0.51  thf('39', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.25/0.51      inference('condensation', [status(thm)], ['38'])).
% 0.25/0.51  thf('40', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X1)
% 0.25/0.51          | ~ (r2_hidden @ (sk_C @ X1 @ (sk_C_1 @ X0)) @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['37', '39'])).
% 0.25/0.51  thf('41', plain,
% 0.25/0.51      (![X0 : $i]:
% 0.25/0.51         ((r1_xboole_0 @ (sk_C_1 @ X0) @ X0)
% 0.25/0.51          | (r1_xboole_0 @ (sk_C_1 @ X0) @ X0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['36', '40'])).
% 0.25/0.51  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ (sk_C_1 @ X0) @ X0)),
% 0.25/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.25/0.51  thf('43', plain, (![X0 : $i]: (r1_xboole_0 @ sk_A @ X0)),
% 0.25/0.51      inference('demod', [status(thm)], ['35', '42'])).
% 0.25/0.51  thf('44', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.51      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.51  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ sk_A @ X0) = (k1_xboole_0))),
% 0.25/0.51      inference('sup-', [status(thm)], ['43', '44'])).
% 0.25/0.51  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.25/0.51      inference('sup+', [status(thm)], ['30', '45'])).
% 0.25/0.51  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('48', plain, ($false),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
