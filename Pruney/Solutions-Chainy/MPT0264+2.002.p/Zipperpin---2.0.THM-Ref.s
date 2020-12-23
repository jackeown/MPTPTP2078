%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJfYgVHc5R

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  49 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  267 ( 323 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X7 ) )
      | ( r2_hidden @ X4 @ X7 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X24 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJfYgVHc5R
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:24:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 76 iterations in 0.043s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(t59_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.51          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.20/0.51             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t100_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X8 @ X9)
% 0.20/0.51           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.51  thf('4', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.51       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X7))
% 0.20/0.51          | (r2_hidden @ X4 @ X7)
% 0.20/0.51          | ~ (r2_hidden @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ sk_B @ X0)
% 0.20/0.51          | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_C_1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_C_1 @ X0))
% 0.20/0.51          | (r2_hidden @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.51        | (r2_hidden @ sk_B @ 
% 0.20/0.51           (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '7'])).
% 0.20/0.51  thf(t90_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (r1_xboole_0 @ (k4_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)) @ X13)),
% 0.20/0.51      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.20/0.51  thf(t47_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.20/0.51           = (k4_xboole_0 @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X2 : $i, X3 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(commutativity_k2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.51  thf(t55_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k2_tarski @ X24 @ X25) @ X26)
% 0.20/0.51          | ~ (r2_hidden @ X24 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ X2))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '17'])).
% 0.20/0.51  thf(d1_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.51          | ((X19) = (X16))
% 0.20/0.51          | ((X18) != (k1_tarski @ X16)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X16 : $i, X19 : $i]:
% 0.20/0.51         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.51  thf('21', plain, (((sk_B) = (sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.51  thf('22', plain, (((sk_A) != (sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
