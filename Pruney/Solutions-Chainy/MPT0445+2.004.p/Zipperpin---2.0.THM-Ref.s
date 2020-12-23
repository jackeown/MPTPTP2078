%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4NxkDmIYka

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:50 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  355 ( 440 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X16 @ X15 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X16 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X16 @ X15 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X16 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relat_1])).

thf('19',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k6_subset_1 @ X11 @ X12 )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['23','24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4NxkDmIYka
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 285 iterations in 0.280s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.51/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.72  thf(fc2_relat_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.51/0.72  thf('0', plain,
% 0.51/0.72      (![X13 : $i, X14 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X13) | (v1_relat_1 @ (k4_xboole_0 @ X13 @ X14)))),
% 0.51/0.72      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.51/0.72  thf(t26_relat_1, axiom,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( v1_relat_1 @ B ) =>
% 0.51/0.72           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.51/0.72             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X15)
% 0.51/0.72          | ((k2_relat_1 @ (k2_xboole_0 @ X16 @ X15))
% 0.51/0.72              = (k2_xboole_0 @ (k2_relat_1 @ X16) @ (k2_relat_1 @ X15)))
% 0.51/0.72          | ~ (v1_relat_1 @ X16))),
% 0.51/0.72      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.51/0.72  thf(commutativity_k2_tarski, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.51/0.72  thf('2', plain,
% 0.51/0.72      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.72  thf(l51_zfmisc_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (![X9 : $i, X10 : $i]:
% 0.51/0.72         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.51/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.72      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      (![X9 : $i, X10 : $i]:
% 0.51/0.72         ((k3_tarski @ (k2_tarski @ X9 @ X10)) = (k2_xboole_0 @ X9 @ X10))),
% 0.51/0.72      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.72  thf('6', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.72      inference('sup+', [status(thm)], ['4', '5'])).
% 0.51/0.72  thf(t7_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.72  thf('7', plain,
% 0.51/0.72      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.51/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.72  thf('8', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['6', '7'])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.51/0.72           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X0))),
% 0.51/0.72      inference('sup+', [status(thm)], ['1', '8'])).
% 0.51/0.72  thf(t39_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.72  thf('10', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.51/0.72           = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.51/0.72  thf('11', plain,
% 0.51/0.72      (![X15 : $i, X16 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X15)
% 0.51/0.72          | ((k2_relat_1 @ (k2_xboole_0 @ X16 @ X15))
% 0.51/0.72              = (k2_xboole_0 @ (k2_relat_1 @ X16) @ (k2_relat_1 @ X15)))
% 0.51/0.72          | ~ (v1_relat_1 @ X16))),
% 0.51/0.72      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.51/0.72  thf(t43_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.51/0.72       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.51/0.72         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.51/0.72          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X0)
% 0.51/0.72          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 0.51/0.72             (k2_relat_1 @ X0)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.72         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.51/0.72          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 0.51/0.72             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.51/0.72          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.72          | ~ (v1_relat_1 @ X1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['10', '13'])).
% 0.51/0.72  thf('15', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X0)
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.72          | (r1_tarski @ 
% 0.51/0.72             (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.51/0.72             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['9', '14'])).
% 0.51/0.72  thf('16', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.51/0.72           (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.51/0.72          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X0))),
% 0.51/0.72      inference('simplify', [status(thm)], ['15'])).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         (~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X1)
% 0.51/0.72          | ~ (v1_relat_1 @ X0)
% 0.51/0.72          | (r1_tarski @ 
% 0.51/0.72             (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 0.51/0.72             (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.51/0.72      inference('sup-', [status(thm)], ['0', '16'])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]:
% 0.51/0.72         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 0.51/0.72           (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.51/0.72          | ~ (v1_relat_1 @ X0)
% 0.51/0.72          | ~ (v1_relat_1 @ X1))),
% 0.51/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.72  thf(t28_relat_1, conjecture,
% 0.51/0.72    (![A:$i]:
% 0.51/0.72     ( ( v1_relat_1 @ A ) =>
% 0.51/0.72       ( ![B:$i]:
% 0.51/0.72         ( ( v1_relat_1 @ B ) =>
% 0.51/0.72           ( r1_tarski @
% 0.51/0.72             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 0.51/0.72             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i]:
% 0.51/0.72        ( ( v1_relat_1 @ A ) =>
% 0.51/0.72          ( ![B:$i]:
% 0.51/0.72            ( ( v1_relat_1 @ B ) =>
% 0.51/0.72              ( r1_tarski @
% 0.51/0.72                ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 0.51/0.72                ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t28_relat_1])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (~ (r1_tarski @ 
% 0.51/0.72          (k6_subset_1 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 0.51/0.72          (k2_relat_1 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(redefinition_k6_subset_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i]:
% 0.51/0.72         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      (![X11 : $i, X12 : $i]:
% 0.51/0.72         ((k6_subset_1 @ X11 @ X12) = (k4_xboole_0 @ X11 @ X12))),
% 0.51/0.72      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.51/0.72  thf('22', plain,
% 0.51/0.72      (~ (r1_tarski @ 
% 0.51/0.72          (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 0.51/0.72          (k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.51/0.72      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.51/0.72  thf('23', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.72      inference('sup-', [status(thm)], ['18', '22'])).
% 0.51/0.72  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf('26', plain, ($false),
% 0.51/0.72      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.51/0.72  
% 0.51/0.72  % SZS output end Refutation
% 0.51/0.72  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
