%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eHUoSAzZSJ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:05 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  298 ( 408 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k3_relat_1 @ X19 ) @ ( k3_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k3_relat_1 @ X19 ) @ ( k3_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eHUoSAzZSJ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.55  % Solved by: fo/fo7.sh
% 0.39/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.55  % done 209 iterations in 0.141s
% 0.39/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.55  % SZS output start Refutation
% 0.39/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.39/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.55  thf(t48_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.55  thf('0', plain,
% 0.39/0.55      (![X7 : $i, X8 : $i]:
% 0.39/0.55         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.39/0.55           = (k3_xboole_0 @ X7 @ X8))),
% 0.39/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.39/0.55  thf(fc2_relat_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]:
% 0.39/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.39/0.55  thf('1', plain,
% 0.39/0.55      (![X16 : $i, X17 : $i]:
% 0.39/0.55         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k4_xboole_0 @ X16 @ X17)))),
% 0.39/0.55      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.39/0.55  thf('2', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]:
% 0.39/0.55         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 0.39/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.39/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.39/0.55  thf('3', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.55  thf('4', plain,
% 0.39/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.39/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.39/0.55  thf(t17_xboole_1, axiom,
% 0.39/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.55  thf('5', plain,
% 0.39/0.55      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.39/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.39/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf(t31_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( v1_relat_1 @ B ) =>
% 0.39/0.56           ( ( r1_tarski @ A @ B ) =>
% 0.39/0.56             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X18)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ X19) @ (k3_relat_1 @ X18))
% 0.39/0.56          | ~ (r1_tarski @ X19 @ X18)
% 0.39/0.56          | ~ (v1_relat_1 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.56             (k3_relat_1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ X1)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.56             (k3_relat_1 @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X1)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.56             (k3_relat_1 @ X1))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '9'])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.56           (k3_relat_1 @ X1))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('sup+', [status(thm)], ['0', '1'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.39/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X18)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ X19) @ (k3_relat_1 @ X18))
% 0.39/0.56          | ~ (r1_tarski @ X19 @ X18)
% 0.39/0.56          | ~ (v1_relat_1 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.56             (k3_relat_1 @ X0))
% 0.39/0.56          | ~ (v1_relat_1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X1)
% 0.39/0.56          | ~ (v1_relat_1 @ X1)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.56             (k3_relat_1 @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['12', '15'])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.56           (k3_relat_1 @ X1))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.56  thf(t19_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.39/0.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X4 @ X5)
% 0.39/0.56          | ~ (r1_tarski @ X4 @ X6)
% 0.39/0.56          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X0)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.56             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.39/0.56          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (v1_relat_1 @ X0)
% 0.39/0.56          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.39/0.56             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.39/0.56          | ~ (v1_relat_1 @ X1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['11', '19'])).
% 0.39/0.56  thf(t34_relat_1, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( v1_relat_1 @ B ) =>
% 0.39/0.56           ( r1_tarski @
% 0.39/0.56             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.39/0.56             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( v1_relat_1 @ A ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( v1_relat_1 @ B ) =>
% 0.39/0.56              ( r1_tarski @
% 0.39/0.56                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.39/0.56                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.39/0.56          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('22', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.56  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('25', plain, ($false),
% 0.39/0.56      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
