%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMdZVxrrVa

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:49 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  280 ( 364 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X8 ) ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RMdZVxrrVa
% 0.15/0.36  % Computer   : n022.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:20:11 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.23/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.53  % Solved by: fo/fo7.sh
% 0.23/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.53  % done 70 iterations in 0.057s
% 0.23/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.53  % SZS output start Refutation
% 0.23/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.53  thf(fc1_relat_1, axiom,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.23/0.53  thf('0', plain,
% 0.23/0.53      (![X18 : $i, X19 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.23/0.53      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.23/0.53  thf(idempotence_k2_xboole_0, axiom,
% 0.23/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.53  thf('1', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.53  thf(t31_xboole_1, axiom,
% 0.23/0.53    (![A:$i,B:$i,C:$i]:
% 0.23/0.53     ( r1_tarski @
% 0.23/0.53       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.23/0.53       ( k2_xboole_0 @ B @ C ) ))).
% 0.23/0.53  thf('2', plain,
% 0.23/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.53         (r1_tarski @ 
% 0.23/0.53          (k2_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X8)) @ 
% 0.23/0.53          (k2_xboole_0 @ X7 @ X8))),
% 0.23/0.53      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.23/0.53  thf('3', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X0))),
% 0.23/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.53  thf('4', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.23/0.53      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.23/0.53  thf('5', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.23/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.53  thf(t25_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) =>
% 0.23/0.53       ( ![B:$i]:
% 0.23/0.53         ( ( v1_relat_1 @ B ) =>
% 0.23/0.53           ( ( r1_tarski @ A @ B ) =>
% 0.23/0.53             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.23/0.53               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.23/0.53  thf('6', plain,
% 0.23/0.53      (![X20 : $i, X21 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ X20)
% 0.23/0.53          | (r1_tarski @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20))
% 0.23/0.53          | ~ (r1_tarski @ X21 @ X20)
% 0.23/0.53          | ~ (v1_relat_1 @ X21))),
% 0.23/0.53      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.23/0.53  thf('7', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.23/0.53          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.23/0.53             (k2_relat_1 @ X0))
% 0.23/0.53          | ~ (v1_relat_1 @ X0))),
% 0.23/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.53  thf('8', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (v1_relat_1 @ X1)
% 0.23/0.53          | ~ (v1_relat_1 @ X0)
% 0.23/0.53          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.23/0.53             (k2_relat_1 @ X0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '7'])).
% 0.23/0.54  thf(t17_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.23/0.54  thf('9', plain,
% 0.23/0.54      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.23/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.23/0.54  thf('10', plain,
% 0.23/0.54      (![X20 : $i, X21 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ X20)
% 0.23/0.54          | (r1_tarski @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20))
% 0.23/0.54          | ~ (r1_tarski @ X21 @ X20)
% 0.23/0.54          | ~ (v1_relat_1 @ X21))),
% 0.23/0.54      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.23/0.54  thf('11', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.23/0.54          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.23/0.54             (k2_relat_1 @ X0))
% 0.23/0.54          | ~ (v1_relat_1 @ X0))),
% 0.23/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.54  thf('12', plain,
% 0.23/0.54      (![X18 : $i, X19 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.23/0.54      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.23/0.54  thf('13', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ X0)
% 0.23/0.54          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.23/0.54             (k2_relat_1 @ X0)))),
% 0.23/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.23/0.54  thf(t19_xboole_1, axiom,
% 0.23/0.54    (![A:$i,B:$i,C:$i]:
% 0.23/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.23/0.54       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.23/0.54  thf('14', plain,
% 0.23/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.23/0.54          | ~ (r1_tarski @ X3 @ X5)
% 0.23/0.54          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.23/0.54      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.23/0.54  thf('15', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ X0)
% 0.23/0.54          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.23/0.54             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 0.23/0.54          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.23/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.54  thf('16', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         (~ (v1_relat_1 @ X0)
% 0.23/0.54          | ~ (v1_relat_1 @ X1)
% 0.23/0.54          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.23/0.54             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.23/0.54          | ~ (v1_relat_1 @ X1))),
% 0.23/0.54      inference('sup-', [status(thm)], ['8', '15'])).
% 0.23/0.54  thf('17', plain,
% 0.23/0.54      (![X0 : $i, X1 : $i]:
% 0.23/0.54         ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.23/0.54           (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.23/0.54          | ~ (v1_relat_1 @ X1)
% 0.23/0.54          | ~ (v1_relat_1 @ X0))),
% 0.23/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.23/0.54  thf(t27_relat_1, conjecture,
% 0.23/0.54    (![A:$i]:
% 0.23/0.54     ( ( v1_relat_1 @ A ) =>
% 0.23/0.54       ( ![B:$i]:
% 0.23/0.54         ( ( v1_relat_1 @ B ) =>
% 0.23/0.54           ( r1_tarski @
% 0.23/0.54             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.23/0.54             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.23/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.54    (~( ![A:$i]:
% 0.23/0.54        ( ( v1_relat_1 @ A ) =>
% 0.23/0.54          ( ![B:$i]:
% 0.23/0.54            ( ( v1_relat_1 @ B ) =>
% 0.23/0.54              ( r1_tarski @
% 0.23/0.54                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.23/0.54                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.23/0.54    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.23/0.54  thf('18', plain,
% 0.23/0.54      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.23/0.54          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('19', plain, ((~ (v1_relat_1 @ sk_B) | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.54  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.54  thf('22', plain, ($false),
% 0.23/0.54      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.54  
% 0.23/0.54  % SZS output end Refutation
% 0.23/0.54  
% 0.23/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
