%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXbezCVBSU

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:18 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  411 ( 595 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k7_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k7_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t169_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
              = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( k5_relat_1 @ ( k7_relat_1 @ A @ C ) @ ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) )
                = ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_1])).

thf('15',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ ( k7_relat_1 @ sk_B @ ( k9_relat_1 @ sk_A @ sk_C ) ) )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ( k5_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
     != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C )
 != ( k7_relat_1 @ ( k5_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tXbezCVBSU
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.33/2.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.52  % Solved by: fo/fo7.sh
% 2.33/2.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.52  % done 1957 iterations in 2.069s
% 2.33/2.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.52  % SZS output start Refutation
% 2.33/2.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.33/2.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.33/2.52  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.33/2.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.33/2.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.33/2.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.33/2.52  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.52  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.33/2.52  thf(t112_relat_1, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ B ) =>
% 2.33/2.52       ( ![C:$i]:
% 2.33/2.52         ( ( v1_relat_1 @ C ) =>
% 2.33/2.52           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 2.33/2.52             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 2.33/2.52  thf('0', plain,
% 2.33/2.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X2)
% 2.33/2.52          | ((k7_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 2.33/2.52              = (k5_relat_1 @ (k7_relat_1 @ X3 @ X4) @ X2))
% 2.33/2.52          | ~ (v1_relat_1 @ X3))),
% 2.33/2.52      inference('cnf', [status(esa)], [t112_relat_1])).
% 2.33/2.52  thf(dt_k7_relat_1, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 2.33/2.52  thf('1', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 2.33/2.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 2.33/2.52  thf(t148_relat_1, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ B ) =>
% 2.33/2.52       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 2.33/2.52  thf('2', plain,
% 2.33/2.52      (![X5 : $i, X6 : $i]:
% 2.33/2.52         (((k2_relat_1 @ (k7_relat_1 @ X5 @ X6)) = (k9_relat_1 @ X5 @ X6))
% 2.33/2.52          | ~ (v1_relat_1 @ X5))),
% 2.33/2.52      inference('cnf', [status(esa)], [t148_relat_1])).
% 2.33/2.52  thf(t94_relat_1, axiom,
% 2.33/2.52    (![A:$i,B:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ B ) =>
% 2.33/2.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 2.33/2.52  thf('3', plain,
% 2.33/2.52      (![X11 : $i, X12 : $i]:
% 2.33/2.52         (((k7_relat_1 @ X12 @ X11) = (k5_relat_1 @ (k6_relat_1 @ X11) @ X12))
% 2.33/2.52          | ~ (v1_relat_1 @ X12))),
% 2.33/2.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 2.33/2.52  thf(t80_relat_1, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ A ) =>
% 2.33/2.52       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 2.33/2.52  thf('4', plain,
% 2.33/2.52      (![X10 : $i]:
% 2.33/2.52         (((k5_relat_1 @ X10 @ (k6_relat_1 @ (k2_relat_1 @ X10))) = (X10))
% 2.33/2.52          | ~ (v1_relat_1 @ X10))),
% 2.33/2.52      inference('cnf', [status(esa)], [t80_relat_1])).
% 2.33/2.52  thf(t55_relat_1, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( v1_relat_1 @ A ) =>
% 2.33/2.52       ( ![B:$i]:
% 2.33/2.52         ( ( v1_relat_1 @ B ) =>
% 2.33/2.52           ( ![C:$i]:
% 2.33/2.52             ( ( v1_relat_1 @ C ) =>
% 2.33/2.52               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.33/2.52                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.33/2.52  thf('5', plain,
% 2.33/2.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X7)
% 2.33/2.52          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 2.33/2.52              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 2.33/2.52          | ~ (v1_relat_1 @ X9)
% 2.33/2.52          | ~ (v1_relat_1 @ X8))),
% 2.33/2.52      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.33/2.52  thf('6', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (((k5_relat_1 @ X0 @ X1)
% 2.33/2.52            = (k5_relat_1 @ X0 @ 
% 2.33/2.52               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X1)
% 2.33/2.52          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 2.33/2.52      inference('sup+', [status(thm)], ['4', '5'])).
% 2.33/2.52  thf(fc3_funct_1, axiom,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.33/2.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.33/2.52  thf('7', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 2.33/2.52      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.33/2.52  thf('8', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (((k5_relat_1 @ X0 @ X1)
% 2.33/2.52            = (k5_relat_1 @ X0 @ 
% 2.33/2.52               (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1)))
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X1))),
% 2.33/2.52      inference('demod', [status(thm)], ['6', '7'])).
% 2.33/2.52  thf('9', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X1)
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ((k5_relat_1 @ X0 @ X1)
% 2.33/2.52              = (k5_relat_1 @ X0 @ 
% 2.33/2.52                 (k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ X1))))),
% 2.33/2.52      inference('simplify', [status(thm)], ['8'])).
% 2.33/2.52  thf('10', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (((k5_relat_1 @ X0 @ X1)
% 2.33/2.52            = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 2.33/2.52          | ~ (v1_relat_1 @ X1)
% 2.33/2.52          | ~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X1))),
% 2.33/2.52      inference('sup+', [status(thm)], ['3', '9'])).
% 2.33/2.52  thf('11', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X0)
% 2.33/2.52          | ~ (v1_relat_1 @ X1)
% 2.33/2.52          | ((k5_relat_1 @ X0 @ X1)
% 2.33/2.52              = (k5_relat_1 @ X0 @ (k7_relat_1 @ X1 @ (k2_relat_1 @ X0)))))),
% 2.33/2.52      inference('simplify', [status(thm)], ['10'])).
% 2.33/2.52  thf('12', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.33/2.52            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.33/2.52               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.33/2.52          | ~ (v1_relat_1 @ X1)
% 2.33/2.52          | ~ (v1_relat_1 @ X2)
% 2.33/2.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 2.33/2.52      inference('sup+', [status(thm)], ['2', '11'])).
% 2.33/2.52  thf('13', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.52         (~ (v1_relat_1 @ X1)
% 2.33/2.52          | ~ (v1_relat_1 @ X2)
% 2.33/2.52          | ~ (v1_relat_1 @ X1)
% 2.33/2.52          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.33/2.52              = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.33/2.52                 (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))))),
% 2.33/2.52      inference('sup-', [status(thm)], ['1', '12'])).
% 2.33/2.52  thf('14', plain,
% 2.33/2.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.52         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.33/2.52            = (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 2.33/2.52               (k7_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 2.33/2.52          | ~ (v1_relat_1 @ X2)
% 2.33/2.52          | ~ (v1_relat_1 @ X1))),
% 2.33/2.52      inference('simplify', [status(thm)], ['13'])).
% 2.33/2.52  thf(t169_funct_1, conjecture,
% 2.33/2.52    (![A:$i]:
% 2.33/2.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.33/2.52       ( ![B:$i]:
% 2.33/2.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.33/2.52           ( ![C:$i]:
% 2.33/2.52             ( ( k5_relat_1 @
% 2.33/2.52                 ( k7_relat_1 @ A @ C ) @ 
% 2.33/2.52                 ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 2.33/2.52               ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ))).
% 2.33/2.52  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.52    (~( ![A:$i]:
% 2.33/2.52        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.33/2.52          ( ![B:$i]:
% 2.33/2.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.33/2.52              ( ![C:$i]:
% 2.33/2.52                ( ( k5_relat_1 @
% 2.33/2.52                    ( k7_relat_1 @ A @ C ) @ 
% 2.33/2.52                    ( k7_relat_1 @ B @ ( k9_relat_1 @ A @ C ) ) ) =
% 2.33/2.52                  ( k7_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) ) ) ) ) ) )),
% 2.33/2.52    inference('cnf.neg', [status(esa)], [t169_funct_1])).
% 2.33/2.52  thf('15', plain,
% 2.33/2.52      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ 
% 2.33/2.52         (k7_relat_1 @ sk_B @ (k9_relat_1 @ sk_A @ sk_C)))
% 2.33/2.52         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('16', plain,
% 2.33/2.52      ((((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 2.33/2.52          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.33/2.52        | ~ (v1_relat_1 @ sk_A)
% 2.33/2.52        | ~ (v1_relat_1 @ sk_B))),
% 2.33/2.52      inference('sup-', [status(thm)], ['14', '15'])).
% 2.33/2.52  thf('17', plain, ((v1_relat_1 @ sk_A)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('19', plain,
% 2.33/2.52      (((k5_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 2.33/2.52         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 2.33/2.52  thf('20', plain,
% 2.33/2.52      ((((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 2.33/2.52          != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))
% 2.33/2.52        | ~ (v1_relat_1 @ sk_A)
% 2.33/2.52        | ~ (v1_relat_1 @ sk_B))),
% 2.33/2.52      inference('sup-', [status(thm)], ['0', '19'])).
% 2.33/2.52  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 2.33/2.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.52  thf('23', plain,
% 2.33/2.52      (((k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C)
% 2.33/2.52         != (k7_relat_1 @ (k5_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.33/2.52  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 2.33/2.52  
% 2.33/2.52  % SZS output end Refutation
% 2.33/2.52  
% 2.33/2.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
