%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YPxlUmwQRA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:33 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   71 (  78 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  448 ( 512 expanded)
%              Number of equality atoms :   47 (  57 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X38 != X37 )
      | ( r2_hidden @ X38 @ X39 )
      | ( X39
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X37: $i] :
      ( r2_hidden @ X37 @ ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k5_xboole_0 @ X6 @ X8 ) )
      | ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','27'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X23 @ X24 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('31',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( X40 = X37 )
      | ( X39
       != ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X37: $i,X40: $i] :
      ( ( X40 = X37 )
      | ~ ( r2_hidden @ X40 @ ( k1_tarski @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YPxlUmwQRA
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 325 iterations in 0.187s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(d1_tarski, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.48/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.48/0.66  thf('0', plain,
% 0.48/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.48/0.66         (((X38) != (X37))
% 0.48/0.66          | (r2_hidden @ X38 @ X39)
% 0.48/0.66          | ((X39) != (k1_tarski @ X37)))),
% 0.48/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.66  thf('1', plain, (![X37 : $i]: (r2_hidden @ X37 @ (k1_tarski @ X37))),
% 0.48/0.66      inference('simplify', [status(thm)], ['0'])).
% 0.48/0.66  thf(t1_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.48/0.66       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.48/0.66         ((r2_hidden @ X5 @ (k5_xboole_0 @ X6 @ X8))
% 0.48/0.66          | (r2_hidden @ X5 @ X6)
% 0.48/0.66          | ~ (r2_hidden @ X5 @ X8))),
% 0.48/0.66      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.48/0.66  thf('3', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((r2_hidden @ X0 @ X1)
% 0.48/0.66          | (r2_hidden @ X0 @ (k5_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.48/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.66  thf(t18_zfmisc_1, conjecture,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.66         ( k1_tarski @ A ) ) =>
% 0.48/0.66       ( ( A ) = ( B ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i]:
% 0.48/0.66        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.66            ( k1_tarski @ A ) ) =>
% 0.48/0.66          ( ( A ) = ( B ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.48/0.66  thf('4', plain,
% 0.48/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.48/0.66         = (k1_tarski @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.48/0.66         = (k1_tarski @ sk_A))),
% 0.48/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.48/0.66  thf(t100_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X9 : $i, X10 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ X9 @ X10)
% 0.48/0.66           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.48/0.66         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.66  thf(t51_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.48/0.66       ( A ) ))).
% 0.48/0.66  thf('9', plain,
% 0.48/0.66      (![X20 : $i, X21 : $i]:
% 0.48/0.66         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 0.48/0.66           = (X20))),
% 0.48/0.66      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.48/0.66  thf(t21_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (![X11 : $i, X12 : $i]:
% 0.48/0.66         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 0.48/0.66      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.48/0.66           = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('sup+', [status(thm)], ['9', '10'])).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.48/0.66           = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('demod', [status(thm)], ['11', '12'])).
% 0.48/0.66  thf('14', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (![X9 : $i, X10 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ X9 @ X10)
% 0.48/0.66           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.66           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['14', '15'])).
% 0.48/0.66  thf('17', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.48/0.66           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.66      inference('sup+', [status(thm)], ['13', '16'])).
% 0.48/0.66  thf(t49_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i,C:$i]:
% 0.48/0.66     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.48/0.66       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 0.48/0.66  thf('18', plain,
% 0.48/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.66         ((k3_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X19))
% 0.48/0.66           = (k4_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ X19))),
% 0.48/0.66      inference('cnf', [status(esa)], [t49_xboole_1])).
% 0.48/0.66  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.66  thf('19', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.48/0.66      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.66  thf('20', plain,
% 0.48/0.66      (![X9 : $i, X10 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ X9 @ X10)
% 0.48/0.66           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.48/0.66      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.66  thf('21', plain,
% 0.48/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.48/0.66  thf(t3_boole, axiom,
% 0.48/0.66    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.66  thf('22', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.48/0.66      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.66  thf(t48_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.66  thf('23', plain,
% 0.48/0.66      (![X15 : $i, X16 : $i]:
% 0.48/0.66         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 0.48/0.66           = (k3_xboole_0 @ X15 @ X16))),
% 0.48/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.66  thf('24', plain,
% 0.48/0.66      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['22', '23'])).
% 0.48/0.66  thf(t2_boole, axiom,
% 0.48/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.66  thf('25', plain,
% 0.48/0.66      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.66  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.48/0.66  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.66      inference('sup+', [status(thm)], ['21', '26'])).
% 0.48/0.66  thf('28', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 0.48/0.66      inference('demod', [status(thm)], ['17', '18', '27'])).
% 0.48/0.66  thf(t75_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.66          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.48/0.66  thf('29', plain,
% 0.48/0.66      (![X23 : $i, X24 : $i]:
% 0.48/0.66         ((r1_xboole_0 @ X23 @ X24)
% 0.48/0.66          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X23 @ X24) @ X24))),
% 0.48/0.66      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.48/0.66  thf('30', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (~ (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.48/0.66          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.66  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.48/0.66  thf('31', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.48/0.66      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.48/0.66  thf(symmetry_r1_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.48/0.66  thf('32', plain,
% 0.48/0.66      (![X3 : $i, X4 : $i]:
% 0.48/0.66         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.48/0.66      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.48/0.66  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.48/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.66  thf('34', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.48/0.66      inference('demod', [status(thm)], ['30', '33'])).
% 0.48/0.66  thf(l24_zfmisc_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.48/0.66  thf('35', plain,
% 0.48/0.66      (![X52 : $i, X53 : $i]:
% 0.48/0.66         (~ (r1_xboole_0 @ (k1_tarski @ X52) @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 0.48/0.66      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.48/0.66  thf('36', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.66  thf('37', plain,
% 0.48/0.66      (~ (r2_hidden @ sk_A @ 
% 0.48/0.66          (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['8', '36'])).
% 0.48/0.66  thf('38', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['3', '37'])).
% 0.48/0.66  thf('39', plain,
% 0.48/0.66      (![X37 : $i, X39 : $i, X40 : $i]:
% 0.48/0.66         (~ (r2_hidden @ X40 @ X39)
% 0.48/0.66          | ((X40) = (X37))
% 0.48/0.66          | ((X39) != (k1_tarski @ X37)))),
% 0.48/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.48/0.66  thf('40', plain,
% 0.48/0.66      (![X37 : $i, X40 : $i]:
% 0.48/0.66         (((X40) = (X37)) | ~ (r2_hidden @ X40 @ (k1_tarski @ X37)))),
% 0.48/0.66      inference('simplify', [status(thm)], ['39'])).
% 0.48/0.66  thf('41', plain, (((sk_A) = (sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['38', '40'])).
% 0.48/0.66  thf('42', plain, (((sk_A) != (sk_B))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf('43', plain, ($false),
% 0.48/0.66      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.48/0.66  
% 0.48/0.66  % SZS output end Refutation
% 0.48/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
