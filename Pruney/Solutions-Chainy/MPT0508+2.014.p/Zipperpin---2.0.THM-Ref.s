%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRbYBLcdTb

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t106_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X9 @ X7 ) @ X8 )
        = ( k7_relat_1 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ ( k7_relat_1 @ X10 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k7_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ ( k7_relat_1 @ X10 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t105_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k7_relat_1 @ sk_D @ X0 ) )
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
      ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
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
      ( ( k2_xboole_0 @ ( k7_relat_1 @ sk_C @ X0 ) @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
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
      ( ~ ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qRbYBLcdTb
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:30:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 76 iterations in 0.125s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.58  thf(t106_relat_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ C ) =>
% 0.20/0.58       ( ![D:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ D ) =>
% 0.20/0.58           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.20/0.58             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.58        ( ( v1_relat_1 @ C ) =>
% 0.20/0.58          ( ![D:$i]:
% 0.20/0.58            ( ( v1_relat_1 @ D ) =>
% 0.20/0.58              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.20/0.58                ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t106_relat_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (~ (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(t102_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ C ) =>
% 0.20/0.58       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.58         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.58         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.58          | ~ (v1_relat_1 @ X9)
% 0.20/0.58          | ((k7_relat_1 @ (k7_relat_1 @ X9 @ X7) @ X8)
% 0.20/0.58              = (k7_relat_1 @ X9 @ X7)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.20/0.58            = (k7_relat_1 @ X0 @ sk_A))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf(t88_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X13 : $i, X14 : $i]:
% 0.20/0.58         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 0.20/0.58      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.58  thf(t105_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ B ) =>
% 0.20/0.58       ( ![C:$i]:
% 0.20/0.58         ( ( v1_relat_1 @ C ) =>
% 0.20/0.58           ( ( r1_tarski @ B @ C ) =>
% 0.20/0.58             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X10)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ X11 @ X12) @ (k7_relat_1 @ X10 @ X12))
% 0.20/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.20/0.58          | ~ (v1_relat_1 @ X11))),
% 0.20/0.58      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.58             (k7_relat_1 @ X0 @ X2))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.58           (k7_relat_1 @ X0 @ X2))
% 0.20/0.58          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.58  thf(dt_k7_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.20/0.58             (k7_relat_1 @ X0 @ X2)))),
% 0.20/0.58      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 0.20/0.58          | ~ (v1_relat_1 @ X0)
% 0.20/0.58          | ~ (v1_relat_1 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['3', '9'])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X0)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.58  thf('12', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X10)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ X11 @ X12) @ (k7_relat_1 @ X10 @ X12))
% 0.20/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.20/0.58          | ~ (v1_relat_1 @ X11))),
% 0.20/0.58      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ sk_C)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))
% 0.20/0.58          | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.58      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.20/0.58  thf(t12_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i]:
% 0.20/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k2_xboole_0 @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))
% 0.20/0.58           = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.58  thf(t11_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.58  thf('21', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         (~ (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1)
% 0.20/0.58          | (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.58        | (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['11', '21'])).
% 0.20/0.58  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      ((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.58  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
