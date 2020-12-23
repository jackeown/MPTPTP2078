%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwoxtQ2tXP

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  344 ( 427 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) @ X6 )
        = ( k7_relat_1 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t189_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
            = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) )
              = ( k7_relat_1 @ A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t189_relat_1])).

thf('12',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
     != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) )
 != ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwoxtQ2tXP
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:41:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 44 iterations in 0.027s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.49  thf(t90_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.22/0.49         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (k7_relat_1 @ X11 @ X12))
% 0.22/0.49            = (k3_xboole_0 @ (k1_relat_1 @ X11) @ X12))
% 0.22/0.49          | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.49  thf(t98_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X13 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (X13))
% 0.22/0.49          | ~ (v1_relat_1 @ X13))),
% 0.22/0.49      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.22/0.49  thf(t87_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X9 : $i, X10 : $i]:
% 0.22/0.49         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X9 @ X10)) @ X10)
% 0.22/0.49          | ~ (v1_relat_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.22/0.49  thf(t103_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ C ) =>
% 0.22/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.22/0.49         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X6 @ X7)
% 0.22/0.49          | ~ (v1_relat_1 @ X8)
% 0.22/0.49          | ((k7_relat_1 @ (k7_relat_1 @ X8 @ X7) @ X6)
% 0.22/0.49              = (k7_relat_1 @ X8 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X1)
% 0.22/0.49          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 0.22/0.49              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.22/0.49              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X1 @ X0)
% 0.22/0.49            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.49          | ((k7_relat_1 @ X1 @ X0)
% 0.22/0.49              = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.49  thf(dt_k7_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X4 : $i, X5 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X4) | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X1 @ X0)
% 0.22/0.49            = (k7_relat_1 @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('clc', [status(thm)], ['6', '7'])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k7_relat_1 @ X1 @ X0)
% 0.22/0.49            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | ~ (v1_relat_1 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['0', '8'])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X1)
% 0.22/0.49          | ((k7_relat_1 @ X1 @ X0)
% 0.22/0.49              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i]:
% 0.22/0.49         (((k1_relat_1 @ (k7_relat_1 @ X11 @ X12))
% 0.22/0.49            = (k3_xboole_0 @ (k1_relat_1 @ X11) @ X12))
% 0.22/0.49          | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.22/0.49  thf(t189_relat_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( v1_relat_1 @ B ) =>
% 0.22/0.49           ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.22/0.49             ( k7_relat_1 @
% 0.22/0.49               A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( v1_relat_1 @ A ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( v1_relat_1 @ B ) =>
% 0.22/0.49              ( ( k7_relat_1 @ A @ ( k1_relat_1 @ B ) ) =
% 0.22/0.49                ( k7_relat_1 @
% 0.22/0.49                  A @ ( k1_relat_1 @ ( k7_relat_1 @ B @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t189_relat_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.49         != (k7_relat_1 @ sk_A @ 
% 0.22/0.49             (k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_relat_1 @ sk_A)))))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.49          != (k7_relat_1 @ sk_A @ 
% 0.22/0.49              (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_A))))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf(commutativity_k2_tarski, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.49  thf(t12_setfam_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((k1_setfam_1 @ (k2_tarski @ X2 @ X3)) = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((k1_setfam_1 @ (k2_tarski @ X2 @ X3)) = (k3_xboole_0 @ X2 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.49         != (k7_relat_1 @ sk_A @ 
% 0.22/0.49             (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.49          != (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '20'])).
% 0.22/0.49  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B))
% 0.22/0.49         != (k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
