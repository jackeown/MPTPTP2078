%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UeZUZvwAL0

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:31 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   50 (  55 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  367 ( 417 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   10 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) @ X15 )
        = ( k7_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ ( k2_zfmisc_1 @ X19 @ ( k2_relat_1 @ X18 ) ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k7_relat_1 @ X20 @ X21 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ ( k2_zfmisc_1 @ X19 @ ( k2_relat_1 @ X18 ) ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('18',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UeZUZvwAL0
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:36:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 130 iterations in 0.070s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.34/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.52  thf(t100_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i,C:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ C ) =>
% 0.34/0.52       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.34/0.52         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.52         (((k7_relat_1 @ (k7_relat_1 @ X13 @ X14) @ X15)
% 0.34/0.52            = (k7_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15)))
% 0.34/0.52          | ~ (v1_relat_1 @ X13))),
% 0.34/0.52      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.34/0.52  thf(t96_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( ( k7_relat_1 @ B @ A ) =
% 0.34/0.52         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.34/0.52  thf('1', plain,
% 0.34/0.52      (![X18 : $i, X19 : $i]:
% 0.34/0.52         (((k7_relat_1 @ X18 @ X19)
% 0.34/0.52            = (k3_xboole_0 @ X18 @ (k2_zfmisc_1 @ X19 @ (k2_relat_1 @ X18))))
% 0.34/0.52          | ~ (v1_relat_1 @ X18))),
% 0.34/0.52      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.34/0.52  thf(t17_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.34/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.34/0.52  thf(t25_relat_1, axiom,
% 0.34/0.52    (![A:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) =>
% 0.34/0.52       ( ![B:$i]:
% 0.34/0.52         ( ( v1_relat_1 @ B ) =>
% 0.34/0.52           ( ( r1_tarski @ A @ B ) =>
% 0.34/0.52             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.34/0.52               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X16 : $i, X17 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X16)
% 0.34/0.52          | (r1_tarski @ (k1_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.34/0.52          | ~ (r1_tarski @ X17 @ X16)
% 0.34/0.52          | ~ (v1_relat_1 @ X17))),
% 0.34/0.52      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.34/0.52  thf('4', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.34/0.52          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.34/0.52             (k1_relat_1 @ X0))
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.52  thf(fc1_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.34/0.52             (k1_relat_1 @ X0)))),
% 0.34/0.52      inference('clc', [status(thm)], ['4', '5'])).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.34/0.52           (k1_relat_1 @ X1))
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | ~ (v1_relat_1 @ X1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['1', '6'])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X1)
% 0.34/0.52          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.34/0.52             (k1_relat_1 @ X1)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.34/0.52  thf(t97_relat_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.34/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      (![X20 : $i, X21 : $i]:
% 0.34/0.52         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.34/0.52          | ((k7_relat_1 @ X20 @ X21) = (X20))
% 0.34/0.52          | ~ (v1_relat_1 @ X20))),
% 0.34/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.34/0.52          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.34/0.52              = (k7_relat_1 @ X0 @ X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (![X18 : $i, X19 : $i]:
% 0.34/0.52         (((k7_relat_1 @ X18 @ X19)
% 0.34/0.52            = (k3_xboole_0 @ X18 @ (k2_zfmisc_1 @ X19 @ (k2_relat_1 @ X18))))
% 0.34/0.52          | ~ (v1_relat_1 @ X18))),
% 0.34/0.52      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (![X11 : $i, X12 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.34/0.52      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.34/0.52          | ~ (v1_relat_1 @ X1)
% 0.34/0.52          | ~ (v1_relat_1 @ X1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X1) | (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.34/0.52            = (k7_relat_1 @ X0 @ X1))
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('clc', [status(thm)], ['10', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.34/0.52            = (k7_relat_1 @ X0 @ X1))
% 0.34/0.52          | ~ (v1_relat_1 @ X0)
% 0.34/0.52          | ~ (v1_relat_1 @ X0))),
% 0.34/0.52      inference('sup+', [status(thm)], ['0', '15'])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (v1_relat_1 @ X0)
% 0.34/0.52          | ((k7_relat_1 @ X0 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.34/0.52              = (k7_relat_1 @ X0 @ X1)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['16'])).
% 0.34/0.52  thf(t192_relat_1, conjecture,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( v1_relat_1 @ B ) =>
% 0.34/0.52       ( ( k7_relat_1 @ B @ A ) =
% 0.34/0.52         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i]:
% 0.34/0.52        ( ( v1_relat_1 @ B ) =>
% 0.34/0.52          ( ( k7_relat_1 @ B @ A ) =
% 0.34/0.52            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (((k7_relat_1 @ sk_B @ sk_A)
% 0.34/0.52         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf(commutativity_k2_tarski, axiom,
% 0.34/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.34/0.52  thf('19', plain,
% 0.34/0.52      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.34/0.52  thf(t12_setfam_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.52  thf('20', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         ((k1_setfam_1 @ (k2_tarski @ X9 @ X10)) = (k3_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.52  thf('23', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      (((k7_relat_1 @ sk_B @ sk_A)
% 0.34/0.52         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['18', '23'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 0.34/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['17', '24'])).
% 0.34/0.52  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 0.34/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.34/0.52  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
