%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t7Pek7uXcx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:46 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :  311 ( 495 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( ( k8_relat_1 @ X10 @ ( k8_relat_1 @ X9 @ X11 ) )
        = ( k8_relat_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X7 @ X8 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k8_relat_1 @ X13 @ X14 ) @ ( k8_relat_1 @ X13 @ X12 ) )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k8_relat_1 @ X13 @ X14 ) @ ( k8_relat_1 @ X13 @ X12 ) )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) )
      = ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ X1 )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t7Pek7uXcx
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 76 iterations in 0.111s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.60  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.42/0.60  thf(t133_relat_1, conjecture,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ C ) =>
% 0.42/0.60       ( ![D:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ D ) =>
% 0.42/0.60           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.42/0.60             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.60        ( ( v1_relat_1 @ C ) =>
% 0.42/0.60          ( ![D:$i]:
% 0.42/0.60            ( ( v1_relat_1 @ D ) =>
% 0.42/0.60              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.42/0.60                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(t129_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ C ) =>
% 0.42/0.60       ( ( r1_tarski @ A @ B ) =>
% 0.42/0.60         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.60         (~ (r1_tarski @ X9 @ X10)
% 0.42/0.60          | ~ (v1_relat_1 @ X11)
% 0.42/0.60          | ((k8_relat_1 @ X10 @ (k8_relat_1 @ X9 @ X11))
% 0.42/0.60              = (k8_relat_1 @ X9 @ X11)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.42/0.60            = (k8_relat_1 @ sk_A @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.60  thf(t117_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X7 : $i, X8 : $i]:
% 0.42/0.60         ((r1_tarski @ (k8_relat_1 @ X7 @ X8) @ X8) | ~ (v1_relat_1 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.42/0.60  thf(t132_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ![C:$i]:
% 0.42/0.60         ( ( v1_relat_1 @ C ) =>
% 0.42/0.60           ( ( r1_tarski @ B @ C ) =>
% 0.42/0.60             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X12)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X13 @ X14) @ (k8_relat_1 @ X13 @ X12))
% 0.42/0.60          | ~ (r1_tarski @ X14 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.42/0.60             (k8_relat_1 @ X2 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.42/0.60           (k8_relat_1 @ X2 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['6'])).
% 0.42/0.60  thf(dt_k8_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X5 : $i, X6 : $i]:
% 0.42/0.60         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.42/0.60             (k8_relat_1 @ X2 @ X0)))),
% 0.42/0.60      inference('clc', [status(thm)], ['7', '8'])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 0.42/0.60          | ~ (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['3', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X0)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['10'])).
% 0.42/0.60  thf('12', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ X12)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X13 @ X14) @ (k8_relat_1 @ X13 @ X12))
% 0.42/0.60          | ~ (r1_tarski @ X14 @ X12)
% 0.42/0.60          | ~ (v1_relat_1 @ X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v1_relat_1 @ sk_C)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))
% 0.42/0.60          | ~ (v1_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.60  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.42/0.60  thf(t12_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.42/0.60  thf('18', plain,
% 0.42/0.60      (![X3 : $i, X4 : $i]:
% 0.42/0.60         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((k2_xboole_0 @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))
% 0.42/0.60           = (k8_relat_1 @ X0 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.60  thf(t11_xboole_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.60         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ X1)
% 0.42/0.60          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ X1))),
% 0.42/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.42/0.60        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['11', '21'])).
% 0.42/0.60  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.60  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.45/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
