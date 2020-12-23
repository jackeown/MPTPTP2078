%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s1VJ4egGkr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 142 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  392 ( 989 expanded)
%              Number of equality atoms :   46 ( 110 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
        = sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X16 @ X18 ) @ X17 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B_1 ) @ sk_B_1 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('26',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('28',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ ( k4_xboole_0 @ X23 @ X24 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_C_1 @ sk_B_1 ) )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('40',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['24','25','40'])).

thf('42',plain,(
    sk_A = sk_C_1 ),
    inference('sup+',[status(thm)],['14','41'])).

thf('43',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s1VJ4egGkr
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 390 iterations in 0.145s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.59  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.59  thf(t1_boole, axiom,
% 0.20/0.59    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.59  thf('1', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.59  thf('2', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.59  thf(t71_xboole_1, conjecture,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.20/0.59         ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.20/0.59       ( ( A ) = ( C ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.59        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ B ) ) & 
% 0.20/0.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.20/0.59          ( ( A ) = ( C ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t71_xboole_1])).
% 0.20/0.59  thf('3', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(d1_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf(t4_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.20/0.59          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('7', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.59  thf(t8_boole, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.59  thf('8', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i]:
% 0.20/0.59         (~ (v1_xboole_0 @ X25) | ~ (v1_xboole_0 @ X26) | ((X25) = (X26)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ sk_A @ sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf(t51_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.20/0.59       ( A ) ))).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      (![X23 : $i, X24 : $i]:
% 0.20/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.20/0.59           = (X23))),
% 0.20/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k2_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_A))
% 0.20/0.59          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      ((((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))
% 0.20/0.59        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['2', '11'])).
% 0.20/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.59  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.59  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('16', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.20/0.59      inference('cnf', [status(esa)], [t1_boole])).
% 0.20/0.59  thf(t46_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20)) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.20/0.59  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.59  thf(t42_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.59       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X16 @ X18) @ X17)
% 0.20/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 0.20/0.59              (k4_xboole_0 @ X18 @ X17)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t42_xboole_1])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.59           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.59  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.20/0.59         = (k4_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['15', '23'])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.59           = (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.59  thf('26', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('28', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_xboole_0 @ sk_A @ sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (((k3_xboole_0 @ sk_A @ sk_B_1) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.59  thf('31', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf(t48_xboole_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (![X21 : $i, X22 : $i]:
% 0.20/0.59         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 0.20/0.59           = (k3_xboole_0 @ X21 @ X22))),
% 0.20/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (((k4_xboole_0 @ sk_A @ sk_A) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.59  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.59  thf('35', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.59  thf('36', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_1 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (![X23 : $i, X24 : $i]:
% 0.20/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ (k4_xboole_0 @ X23 @ X24))
% 0.20/0.59           = (X23))),
% 0.20/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_C_1 @ sk_B_1))
% 0.20/0.59         = (sk_C_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.59      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.59  thf('40', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('41', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_C_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '25', '40'])).
% 0.20/0.59  thf('42', plain, (((sk_A) = (sk_C_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['14', '41'])).
% 0.20/0.59  thf('43', plain, (((sk_A) != (sk_C_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('44', plain, ($false),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
