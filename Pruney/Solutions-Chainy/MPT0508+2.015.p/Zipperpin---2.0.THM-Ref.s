%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7atXYWDP4

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  49 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  286 ( 470 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X5 ) @ X6 )
        = ( k7_relat_1 @ X7 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X11 @ X12 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t105_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k7_relat_1 @ X9 @ X10 ) @ ( k7_relat_1 @ X8 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k7_relat_1 @ X9 @ X10 ) @ ( k7_relat_1 @ X8 @ X10 ) )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7atXYWDP4
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:04:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 40 iterations in 0.044s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(t106_relat_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( v1_relat_1 @ D ) =>
% 0.19/0.49           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.19/0.49             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ C ) =>
% 0.19/0.49          ( ![D:$i]:
% 0.19/0.49            ( ( v1_relat_1 @ D ) =>
% 0.19/0.49              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.19/0.49                ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t106_relat_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (~ (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t102_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X5 @ X6)
% 0.19/0.49          | ~ (v1_relat_1 @ X7)
% 0.19/0.49          | ((k7_relat_1 @ (k7_relat_1 @ X7 @ X5) @ X6)
% 0.19/0.49              = (k7_relat_1 @ X7 @ X5)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 0.19/0.49            = (k7_relat_1 @ X0 @ sk_A))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(t88_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         ((r1_tarski @ (k7_relat_1 @ X11 @ X12) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.19/0.49      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.49  thf(t105_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( v1_relat_1 @ C ) =>
% 0.19/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.19/0.49             ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ ( k7_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X8)
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ X9 @ X10) @ (k7_relat_1 @ X8 @ X10))
% 0.19/0.49          | ~ (r1_tarski @ X9 @ X8)
% 0.19/0.49          | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.19/0.49             (k7_relat_1 @ X0 @ X2))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.19/0.49           (k7_relat_1 @ X0 @ X2))
% 0.19/0.49          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.49  thf(dt_k7_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X3) | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X2) @ 
% 0.19/0.49             (k7_relat_1 @ X0 @ X2)))),
% 0.19/0.49      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B))
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['3', '9'])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ (k7_relat_1 @ X0 @ sk_B)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.49  thf('12', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X8)
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ X9 @ X10) @ (k7_relat_1 @ X8 @ X10))
% 0.19/0.49          | ~ (r1_tarski @ X9 @ X8)
% 0.19/0.49          | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t105_relat_1])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ sk_C)
% 0.19/0.49          | (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ (k7_relat_1 @ sk_D @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.49  thf(t1_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.49       ( r1_tarski @ A @ C ) ))).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.49          | (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ (k7_relat_1 @ sk_C @ X0) @ X1)
% 0.19/0.49          | ~ (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.49        | (r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '19'])).
% 0.19/0.49  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      ((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
