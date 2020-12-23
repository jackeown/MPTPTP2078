%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TJ8gwxoO48

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:29 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  301 ( 362 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t155_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_relat_1])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_C_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) @ ( k9_relat_1 @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TJ8gwxoO48
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.75  % Solved by: fo/fo7.sh
% 0.59/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.75  % done 246 iterations in 0.298s
% 0.59/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.75  % SZS output start Refutation
% 0.59/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.75  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.59/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.75  thf(t153_relat_1, axiom,
% 0.59/0.75    (![A:$i,B:$i,C:$i]:
% 0.59/0.75     ( ( v1_relat_1 @ C ) =>
% 0.59/0.75       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.59/0.75         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.59/0.75  thf('0', plain,
% 0.59/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.75         (((k9_relat_1 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.59/0.75            = (k2_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ 
% 0.59/0.75               (k9_relat_1 @ X14 @ X16)))
% 0.59/0.75          | ~ (v1_relat_1 @ X14))),
% 0.59/0.75      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.59/0.75  thf(d3_tarski, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.75  thf('1', plain,
% 0.59/0.75      (![X1 : $i, X3 : $i]:
% 0.59/0.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.75  thf('2', plain,
% 0.59/0.75      (![X1 : $i, X3 : $i]:
% 0.59/0.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.75      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.75  thf('3', plain,
% 0.59/0.75      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.59/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.75  thf('4', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.75      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.75  thf(t10_xboole_1, axiom,
% 0.59/0.75    (![A:$i,B:$i,C:$i]:
% 0.59/0.75     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.59/0.75  thf('5', plain,
% 0.59/0.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.59/0.75         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.59/0.75      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.59/0.75  thf('6', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.59/0.75      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.75  thf('7', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.75         ((r1_tarski @ (k9_relat_1 @ X2 @ X0) @ 
% 0.59/0.75           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.59/0.75          | ~ (v1_relat_1 @ X2))),
% 0.59/0.75      inference('sup+', [status(thm)], ['0', '6'])).
% 0.59/0.75  thf(t39_xboole_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]:
% 0.59/0.75     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.75  thf('8', plain,
% 0.59/0.75      (![X7 : $i, X8 : $i]:
% 0.59/0.75         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 0.59/0.75           = (k2_xboole_0 @ X7 @ X8))),
% 0.59/0.75      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.59/0.75  thf('9', plain,
% 0.59/0.75      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.75         (((k9_relat_1 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.59/0.75            = (k2_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ 
% 0.59/0.75               (k9_relat_1 @ X14 @ X16)))
% 0.59/0.75          | ~ (v1_relat_1 @ X14))),
% 0.59/0.75      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.59/0.75  thf(t43_xboole_1, axiom,
% 0.59/0.75    (![A:$i,B:$i,C:$i]:
% 0.59/0.75     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.59/0.75       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.59/0.75  thf('10', plain,
% 0.59/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.75         ((r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.59/0.75          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.59/0.75      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.59/0.75  thf('11', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.75         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.59/0.75          | ~ (v1_relat_1 @ X2)
% 0.59/0.75          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.59/0.75             (k9_relat_1 @ X2 @ X0)))),
% 0.59/0.75      inference('sup-', [status(thm)], ['9', '10'])).
% 0.59/0.75  thf('12', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.75         (~ (r1_tarski @ X3 @ (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.59/0.75          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.59/0.75             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.59/0.75          | ~ (v1_relat_1 @ X2))),
% 0.59/0.75      inference('sup-', [status(thm)], ['8', '11'])).
% 0.59/0.75  thf('13', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.75         (~ (v1_relat_1 @ X2)
% 0.59/0.75          | ~ (v1_relat_1 @ X2)
% 0.59/0.75          | (r1_tarski @ 
% 0.59/0.75             (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.59/0.75             (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.59/0.75      inference('sup-', [status(thm)], ['7', '12'])).
% 0.59/0.75  thf('14', plain,
% 0.59/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.75         ((r1_tarski @ 
% 0.59/0.75           (k4_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.59/0.75           (k9_relat_1 @ X2 @ (k4_xboole_0 @ X0 @ X1)))
% 0.59/0.75          | ~ (v1_relat_1 @ X2))),
% 0.59/0.75      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.75  thf(t155_relat_1, conjecture,
% 0.59/0.75    (![A:$i,B:$i,C:$i]:
% 0.59/0.75     ( ( v1_relat_1 @ C ) =>
% 0.59/0.75       ( r1_tarski @
% 0.59/0.75         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.59/0.75         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 0.59/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.75        ( ( v1_relat_1 @ C ) =>
% 0.59/0.75          ( r1_tarski @
% 0.59/0.75            ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.59/0.75            ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )),
% 0.59/0.75    inference('cnf.neg', [status(esa)], [t155_relat_1])).
% 0.59/0.75  thf('15', plain,
% 0.59/0.75      (~ (r1_tarski @ 
% 0.59/0.75          (k6_subset_1 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.59/0.75           (k9_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.59/0.75          (k9_relat_1 @ sk_C_1 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf(redefinition_k6_subset_1, axiom,
% 0.59/0.75    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.59/0.75  thf('16', plain,
% 0.59/0.75      (![X12 : $i, X13 : $i]:
% 0.59/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.59/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.59/0.75  thf('17', plain,
% 0.59/0.75      (![X12 : $i, X13 : $i]:
% 0.59/0.75         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.59/0.75      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.59/0.75  thf('18', plain,
% 0.59/0.75      (~ (r1_tarski @ 
% 0.59/0.75          (k4_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.59/0.75           (k9_relat_1 @ sk_C_1 @ sk_B)) @ 
% 0.59/0.75          (k9_relat_1 @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.59/0.75      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.59/0.75  thf('19', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.59/0.75      inference('sup-', [status(thm)], ['14', '18'])).
% 0.59/0.75  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.59/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.75  thf('21', plain, ($false), inference('demod', [status(thm)], ['19', '20'])).
% 0.59/0.75  
% 0.59/0.75  % SZS output end Refutation
% 0.59/0.75  
% 0.59/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
