%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2EkptmDF2

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:09 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   61 (  71 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  357 ( 440 expanded)
%              Number of equality atoms :   40 (  46 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ C ) )
       => ( r1_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X27: $i] :
      ( r1_xboole_0 @ X27 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['5','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    r1_xboole_0 @ sk_A @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k4_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','24'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('29',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ X28 @ ( k2_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o2EkptmDF2
% 0.16/0.38  % Computer   : n020.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 11:53:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 99 iterations in 0.050s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.23/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(t73_xboole_1, conjecture,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.23/0.53       ( r1_tarski @ A @ B ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.53        ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.53            ( r1_xboole_0 @ A @ C ) ) =>
% 0.23/0.53          ( r1_tarski @ A @ B ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t73_xboole_1])).
% 0.23/0.53  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('1', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf(t12_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X13 : $i, X14 : $i]:
% 0.23/0.53         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.23/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (((k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.23/0.53         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf(t40_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('4', plain,
% 0.23/0.53      (![X18 : $i, X19 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.23/0.53           = (k4_xboole_0 @ X18 @ X19))),
% 0.23/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 0.23/0.53         (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.23/0.53         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf(t3_boole, axiom,
% 0.23/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.53  thf('6', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.53  thf(t48_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      (![X25 : $i, X26 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 0.23/0.53           = (k3_xboole_0 @ X25 @ X26))),
% 0.23/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['6', '7'])).
% 0.23/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.53  thf('9', plain, (![X27 : $i]: (r1_xboole_0 @ X27 @ k1_xboole_0)),
% 0.23/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.53  thf(d7_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.53  thf('10', plain,
% 0.23/0.53      (![X2 : $i, X3 : $i]:
% 0.23/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.23/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.53  thf('11', plain,
% 0.23/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.53  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['8', '11'])).
% 0.23/0.53  thf('13', plain,
% 0.23/0.53      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.23/0.53      inference('demod', [status(thm)], ['5', '12'])).
% 0.23/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.23/0.53  thf('14', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.53  thf('15', plain, ((r1_xboole_0 @ sk_A @ sk_C_2)),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('16', plain,
% 0.23/0.53      (![X2 : $i, X3 : $i]:
% 0.23/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.23/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.53  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_C_2) = (k1_xboole_0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.53  thf(t47_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('18', plain,
% 0.23/0.53      (![X23 : $i, X24 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.23/0.53           = (k4_xboole_0 @ X23 @ X24))),
% 0.23/0.53      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.23/0.53  thf('19', plain,
% 0.23/0.53      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.23/0.53      inference('sup+', [status(thm)], ['17', '18'])).
% 0.23/0.53  thf('20', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.53  thf('21', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 0.23/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.23/0.53  thf(t41_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.23/0.53       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.23/0.53           = (k4_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ sk_A @ X0)
% 0.23/0.53           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['21', '22'])).
% 0.23/0.53  thf('24', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ sk_A @ X0)
% 0.23/0.53           = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ X0 @ sk_C_2)))),
% 0.23/0.53      inference('sup+', [status(thm)], ['14', '23'])).
% 0.23/0.53  thf('25', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.53      inference('demod', [status(thm)], ['13', '24'])).
% 0.23/0.53  thf(t39_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      (![X15 : $i, X16 : $i]:
% 0.23/0.53         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.23/0.53           = (k2_xboole_0 @ X15 @ X16))),
% 0.23/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.23/0.53  thf('27', plain,
% 0.23/0.53      (((k2_xboole_0 @ sk_B @ k1_xboole_0) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      (![X18 : $i, X19 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.23/0.53           = (k4_xboole_0 @ X18 @ X19))),
% 0.23/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.23/0.53  thf('29', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.23/0.53  thf('31', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.23/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.53  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('33', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ sk_A))),
% 0.23/0.53      inference('demod', [status(thm)], ['27', '32'])).
% 0.23/0.53  thf('34', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.23/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.23/0.53  thf(t7_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      (![X28 : $i, X29 : $i]: (r1_tarski @ X28 @ (k2_xboole_0 @ X28 @ X29))),
% 0.23/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.23/0.53  thf('37', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.53      inference('sup+', [status(thm)], ['33', '36'])).
% 0.23/0.53  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
