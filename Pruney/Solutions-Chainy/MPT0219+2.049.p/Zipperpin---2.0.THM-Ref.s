%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fPPxz0HdFH

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:10 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 222 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  531 (1631 expanded)
%              Number of equality atoms :   66 ( 195 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X37 != X36 )
      | ( r2_hidden @ X37 @ X38 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X36: $i] :
      ( r2_hidden @ X36 @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('29',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','32'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,(
    ! [X36: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X39 @ X38 )
      | ( X39 = X36 )
      | ( X38
       != ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('51',plain,(
    ! [X36: $i,X39: $i] :
      ( ( X39 = X36 )
      | ~ ( r2_hidden @ X39 @ ( k1_tarski @ X36 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fPPxz0HdFH
% 0.13/0.37  % Computer   : n006.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:49:08 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 210 iterations in 0.144s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(d1_tarski, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.62         (((X37) != (X36))
% 0.44/0.62          | (r2_hidden @ X37 @ X38)
% 0.44/0.62          | ((X38) != (k1_tarski @ X36)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.62  thf('1', plain, (![X36 : $i]: (r2_hidden @ X36 @ (k1_tarski @ X36))),
% 0.44/0.62      inference('simplify', [status(thm)], ['0'])).
% 0.44/0.62  thf(t13_zfmisc_1, conjecture,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.44/0.62         ( k1_tarski @ A ) ) =>
% 0.44/0.62       ( ( A ) = ( B ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i,B:$i]:
% 0.44/0.62        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.44/0.62            ( k1_tarski @ A ) ) =>
% 0.44/0.62          ( ( A ) = ( B ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.44/0.62         = (k1_tarski @ sk_A))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t98_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X22 : $i, X23 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X22 @ X23)
% 0.44/0.62           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.62  thf('4', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.44/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.44/0.62  thf(t100_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.62  thf('5', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.62           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.62  thf('6', plain,
% 0.44/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf(t91_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.44/0.62       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.62         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.44/0.62           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.44/0.62           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      (![X22 : $i, X23 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X22 @ X23)
% 0.44/0.62           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.62  thf(t36_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.44/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.62  thf(t28_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X12 : $i, X13 : $i]:
% 0.44/0.62         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.44/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.44/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.44/0.62  thf('13', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.44/0.62           = (k4_xboole_0 @ X0 @ X1))),
% 0.44/0.62      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.62  thf('15', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.62           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.44/0.62           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.44/0.62           = (k2_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['9', '16'])).
% 0.44/0.62  thf(idempotence_k2_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.62  thf('18', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf(t38_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.44/0.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.62  thf('20', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i]:
% 0.44/0.62         (((X16) = (k1_xboole_0))
% 0.44/0.62          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.44/0.62          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 0.44/0.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.44/0.62  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k5_xboole_0 @ k1_xboole_0 @ X1)
% 0.44/0.62           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['8', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.44/0.62           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0)
% 0.44/0.62           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      (![X22 : $i, X23 : $i]:
% 0.44/0.62         ((k2_xboole_0 @ X22 @ X23)
% 0.44/0.62           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.62  thf('29', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 0.44/0.62      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      (![X0 : $i]: ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X0) = (X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.44/0.62  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.44/0.62  thf('33', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['24', '32'])).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X0 @ X1)
% 0.44/0.62           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['3', '33'])).
% 0.44/0.62  thf('35', plain,
% 0.44/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.44/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['2', '34'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.62  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('38', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['36', '37'])).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.44/0.62      inference('demod', [status(thm)], ['35', '38'])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i]:
% 0.44/0.62         ((k4_xboole_0 @ X10 @ X11)
% 0.44/0.62           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['24', '32'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      (![X0 : $i, X1 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ X1 @ X0)
% 0.44/0.62           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.44/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.44/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.44/0.62      inference('sup+', [status(thm)], ['39', '42'])).
% 0.44/0.62  thf(t5_boole, axiom,
% 0.44/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.62  thf('44', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.44/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.44/0.62         = (k1_tarski @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['43', '44'])).
% 0.44/0.62  thf(d4_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.44/0.62       ( ![D:$i]:
% 0.44/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.44/0.62  thf('46', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X6 @ X5)
% 0.44/0.62          | (r2_hidden @ X6 @ X4)
% 0.44/0.62          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.44/0.62  thf('47', plain,
% 0.44/0.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.44/0.62         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.44/0.62          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['45', '47'])).
% 0.44/0.62  thf('49', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '48'])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (![X36 : $i, X38 : $i, X39 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X39 @ X38)
% 0.44/0.62          | ((X39) = (X36))
% 0.44/0.62          | ((X38) != (k1_tarski @ X36)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X36 : $i, X39 : $i]:
% 0.44/0.62         (((X39) = (X36)) | ~ (r2_hidden @ X39 @ (k1_tarski @ X36)))),
% 0.44/0.62      inference('simplify', [status(thm)], ['50'])).
% 0.44/0.62  thf('52', plain, (((sk_B) = (sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['49', '51'])).
% 0.44/0.62  thf('53', plain, (((sk_A) != (sk_B))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('54', plain, ($false),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
