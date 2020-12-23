%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zKoNSA0wOT

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  390 ( 726 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t97_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
            = ( k8_relat_1 @ A @ C ) )
          & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
            = ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
              = ( k8_relat_1 @ A @ C ) )
            & ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
              = ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X7 @ X8 ) ) @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k8_relat_1 @ X10 @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k8_relat_1 @ X11 @ ( k8_relat_1 @ X12 @ X13 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('15',plain,
    ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('16',plain,
    ( ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
       != ( k8_relat_1 @ sk_A @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k8_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
   <= ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
    = ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B @ sk_C ) )
     != ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['9'])).

thf('22',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ sk_C ) )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['10','22'])).

thf('24',plain,
    ( ( ( k8_relat_1 @ sk_A @ sk_C )
     != ( k8_relat_1 @ sk_A @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k8_relat_1 @ sk_A @ sk_C )
 != ( k8_relat_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zKoNSA0wOT
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 41 iterations in 0.034s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(t97_funct_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49         ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.19/0.49             ( k8_relat_1 @ A @ C ) ) & 
% 0.19/0.49           ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.19/0.49             ( k8_relat_1 @ A @ C ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49          ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49            ( ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) =
% 0.19/0.49                ( k8_relat_1 @ A @ C ) ) & 
% 0.19/0.49              ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.19/0.49                ( k8_relat_1 @ A @ C ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t97_funct_1])).
% 0.19/0.49  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t116_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i]:
% 0.19/0.49         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X7 @ X8)) @ X7)
% 0.19/0.49          | ~ (v1_relat_1 @ X8))),
% 0.19/0.49      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.19/0.49  thf(t1_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.49       ( r1_tarski @ A @ C ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.49          | (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X1)
% 0.19/0.49          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2)
% 0.19/0.49          | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.19/0.49  thf(t125_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.19/0.49         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]:
% 0.19/0.49         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.19/0.49          | ((k8_relat_1 @ X10 @ X9) = (X9))
% 0.19/0.49          | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49              = (k8_relat_1 @ sk_A @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(dt_k8_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i]:
% 0.19/0.49         ((v1_relat_1 @ (k8_relat_1 @ X5 @ X6)) | ~ (v1_relat_1 @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49            = (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('clc', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49          != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49        | ((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49            != (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['9'])).
% 0.19/0.49  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf(t127_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.19/0.49         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.49         (((k8_relat_1 @ X11 @ (k8_relat_1 @ X12 @ X13))
% 0.19/0.49            = (k8_relat_1 @ (k3_xboole_0 @ X11 @ X12) @ X13))
% 0.19/0.49          | ~ (v1_relat_1 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('split', [status(esa)], ['9'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.49           != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49         | ~ (v1_relat_1 @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      ((((k8_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 0.19/0.49          != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49                = (k8_relat_1 @ sk_A @ sk_C))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['13', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (~
% 0.19/0.49       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49          = (k8_relat_1 @ sk_A @ sk_C))) | 
% 0.19/0.49       ~
% 0.19/0.49       (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B @ sk_C))
% 0.19/0.49          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('split', [status(esa)], ['9'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (~
% 0.19/0.49       (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49          = (k8_relat_1 @ sk_A @ sk_C)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49         != (k8_relat_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['10', '22'])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '23'])).
% 0.19/0.49  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (((k8_relat_1 @ sk_A @ sk_C) != (k8_relat_1 @ sk_A @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
