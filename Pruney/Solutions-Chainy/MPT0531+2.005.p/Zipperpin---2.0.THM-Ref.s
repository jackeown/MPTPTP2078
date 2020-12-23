%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DrS5asf8KA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 ( 235 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t131_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X4 @ X5 ) )
      = ( k3_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('6',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X14 @ ( k8_relat_1 @ X15 @ X16 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X12 @ X13 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X10 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DrS5asf8KA
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 39 iterations in 0.023s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.46  thf(t131_relat_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ C ) =>
% 0.20/0.46          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.46            ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t131_relat_1])).
% 0.20/0.46  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(l32_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.46  thf('2', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf(t48_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X4 @ X5))
% 0.20/0.46           = (k3_xboole_0 @ X4 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t3_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.46  thf('5', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.46  thf('6', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(t127_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.20/0.46         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.46         (((k8_relat_1 @ X14 @ (k8_relat_1 @ X15 @ X16))
% 0.20/0.46            = (k8_relat_1 @ (k3_xboole_0 @ X14 @ X15) @ X16))
% 0.20/0.46          | ~ (v1_relat_1 @ X16))),
% 0.20/0.46      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.20/0.46  thf(t117_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X12 : $i, X13 : $i]:
% 0.20/0.46         ((r1_tarski @ (k8_relat_1 @ X12 @ X13) @ X13) | ~ (v1_relat_1 @ X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         ((r1_tarski @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.20/0.46           (k8_relat_1 @ X1 @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf(dt_k8_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         ((v1_relat_1 @ (k8_relat_1 @ X10 @ X11)) | ~ (v1_relat_1 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r1_tarski @ (k8_relat_1 @ (k3_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.20/0.46             (k8_relat_1 @ X1 @ X0)))),
% 0.20/0.46      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 0.20/0.46          | ~ (v1_relat_1 @ X0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['6', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain, (~ (v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
