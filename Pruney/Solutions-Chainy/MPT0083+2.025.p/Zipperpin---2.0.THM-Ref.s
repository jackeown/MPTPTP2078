%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfGkTYKqMC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:18 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   68 (  96 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 ( 660 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t76_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ B )
       => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_A ) @ ( k3_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( r1_xboole_0 @ X24 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( sk_B_1
      = ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ X25 @ X26 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X25 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YfGkTYKqMC
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.90/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.11  % Solved by: fo/fo7.sh
% 0.90/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.11  % done 1665 iterations in 0.656s
% 0.90/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.11  % SZS output start Refutation
% 0.90/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.11  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.11  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.11  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.11  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.90/1.11  thf(t76_xboole_1, conjecture,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( r1_xboole_0 @ A @ B ) =>
% 0.90/1.11       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 0.90/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.11        ( ( r1_xboole_0 @ A @ B ) =>
% 0.90/1.11          ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )),
% 0.90/1.11    inference('cnf.neg', [status(esa)], [t76_xboole_1])).
% 0.90/1.11  thf('0', plain,
% 0.90/1.11      (~ (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_A) @ 
% 0.90/1.11          (k3_xboole_0 @ sk_C_2 @ sk_B_1))),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.90/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.11  thf(t7_xboole_0, axiom,
% 0.90/1.11    (![A:$i]:
% 0.90/1.11     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.90/1.11          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.90/1.11  thf('2', plain,
% 0.90/1.11      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.90/1.11      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.90/1.11  thf(t4_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.11            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.90/1.11  thf('3', plain,
% 0.90/1.11      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.90/1.11          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.11  thf('4', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('5', plain, (((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['1', '4'])).
% 0.90/1.11  thf(t16_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.90/1.11       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.90/1.11  thf('6', plain,
% 0.90/1.11      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.90/1.11           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.90/1.11  thf('7', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.90/1.11           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['5', '6'])).
% 0.90/1.11  thf(t3_xboole_0, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.90/1.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.11            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.90/1.11  thf('8', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.11  thf(t2_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.11  thf('9', plain,
% 0.90/1.11      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.11  thf('10', plain,
% 0.90/1.11      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.90/1.11          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.90/1.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.90/1.11  thf('11', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.11  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.90/1.11  thf('12', plain, (![X24 : $i]: (r1_xboole_0 @ X24 @ k1_xboole_0)),
% 0.90/1.11      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.90/1.11  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.90/1.11      inference('demod', [status(thm)], ['11', '12'])).
% 0.90/1.11  thf('14', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['8', '13'])).
% 0.90/1.11  thf('15', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.11  thf('16', plain,
% 0.90/1.11      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.11  thf('17', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['7', '16'])).
% 0.90/1.11  thf(t47_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.11  thf('18', plain,
% 0.90/1.11      (![X19 : $i, X20 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.90/1.11           = (k4_xboole_0 @ X19 @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.11  thf('19', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.90/1.11           = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['17', '18'])).
% 0.90/1.11  thf(t3_boole, axiom,
% 0.90/1.11    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.90/1.11  thf('20', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.11  thf('21', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((sk_A) = (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 0.90/1.11      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.11  thf(t17_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.90/1.11  thf('22', plain,
% 0.90/1.11      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.90/1.11      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.90/1.11  thf(t37_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.11  thf('23', plain,
% 0.90/1.11      (![X15 : $i, X17 : $i]:
% 0.90/1.11         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 0.90/1.11          | ~ (r1_tarski @ X15 @ X17))),
% 0.90/1.11      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.90/1.11  thf('24', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.90/1.11      inference('sup-', [status(thm)], ['22', '23'])).
% 0.90/1.11  thf(t49_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i,C:$i]:
% 0.90/1.11     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.90/1.11       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.90/1.11  thf('25', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.90/1.11           = (k4_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23))),
% 0.90/1.11      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.90/1.11  thf('26', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.11  thf('27', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ X0) @ sk_A) = (k1_xboole_0))),
% 0.90/1.11      inference('sup+', [status(thm)], ['21', '26'])).
% 0.90/1.11  thf('28', plain,
% 0.90/1.11      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.90/1.11           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.90/1.11      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.90/1.11  thf('29', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ X0 @ sk_A)) = (k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['27', '28'])).
% 0.90/1.11  thf('30', plain,
% 0.90/1.11      (![X19 : $i, X20 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X19 @ X20))
% 0.90/1.11           = (k4_xboole_0 @ X19 @ X20))),
% 0.90/1.11      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.90/1.11  thf('31', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((k4_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.90/1.11           = (k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['29', '30'])).
% 0.90/1.11  thf('32', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.90/1.11      inference('cnf', [status(esa)], [t3_boole])).
% 0.90/1.11  thf('33', plain,
% 0.90/1.11      (![X0 : $i]:
% 0.90/1.11         ((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ X0 @ sk_A)))),
% 0.90/1.11      inference('demod', [status(thm)], ['31', '32'])).
% 0.90/1.11  thf('34', plain,
% 0.90/1.11      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.90/1.11           = (k4_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23))),
% 0.90/1.11      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.90/1.11  thf('35', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.90/1.11      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.11  thf(t75_xboole_1, axiom,
% 0.90/1.11    (![A:$i,B:$i]:
% 0.90/1.11     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.11          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.90/1.11  thf('36', plain,
% 0.90/1.11      (![X25 : $i, X26 : $i]:
% 0.90/1.11         ((r1_xboole_0 @ X25 @ X26)
% 0.90/1.11          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X25 @ X26) @ X26))),
% 0.90/1.11      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.90/1.11  thf('37', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (~ (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.90/1.11          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.11  thf('38', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.90/1.11      inference('sup-', [status(thm)], ['8', '13'])).
% 0.90/1.11  thf('39', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.90/1.11      inference('demod', [status(thm)], ['37', '38'])).
% 0.90/1.11  thf('40', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.11         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.90/1.11      inference('sup+', [status(thm)], ['34', '39'])).
% 0.90/1.11  thf('41', plain,
% 0.90/1.11      (![X0 : $i, X1 : $i]:
% 0.90/1.11         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X1 @ sk_B_1))),
% 0.90/1.11      inference('sup+', [status(thm)], ['33', '40'])).
% 0.90/1.11  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.90/1.11  
% 0.90/1.11  % SZS output end Refutation
% 0.90/1.11  
% 0.90/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
