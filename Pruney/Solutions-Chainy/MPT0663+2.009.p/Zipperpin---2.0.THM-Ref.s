%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JPoPx2PjgL

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  69 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  474 ( 643 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t198_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) )
                  = ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ X3 )
       != ( k1_relat_1 @ X2 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X3 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X4 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ ( k6_relat_1 @ X11 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ X8 @ X7 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X7 ) @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('19',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X9: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','17','18','19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X14 @ X15 ) @ X13 )
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
        = ( k1_funct_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','26'])).

thf('28',plain,
    ( ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JPoPx2PjgL
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 23 iterations in 0.022s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(t71_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.47         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.20/0.47            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.20/0.47              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.47  thf(t94_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X8 @ X7) = (k5_relat_1 @ (k6_relat_1 @ X7) @ X8))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X8 @ X7) = (k5_relat_1 @ (k6_relat_1 @ X7) @ X8))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf(t71_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf('6', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf(t198_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( v1_relat_1 @ C ) =>
% 0.20/0.47               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.20/0.47                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.20/0.47                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X2)
% 0.20/0.47          | ((k1_relat_1 @ X3) != (k1_relat_1 @ X2))
% 0.20/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X4 @ X3))
% 0.20/0.47              = (k1_relat_1 @ (k5_relat_1 @ X4 @ X2)))
% 0.20/0.47          | ~ (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (((X0) != (k1_relat_1 @ X1))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X2)
% 0.20/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.20/0.47              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(fc3_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('9', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (((X0) != (k1_relat_1 @ X1))
% 0.20/0.47          | ~ (v1_relat_1 @ X2)
% 0.20/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X0)))
% 0.20/0.47              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ (k1_relat_1 @ X1))))
% 0.20/0.47              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ X2))),
% 0.20/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)) @ X0))
% 0.20/0.47            = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['5', '11'])).
% 0.20/0.47  thf(t43_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.47       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X11 : $i, X12 : $i]:
% 0.20/0.47         ((k5_relat_1 @ (k6_relat_1 @ X12) @ (k6_relat_1 @ X11))
% 0.20/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i]:
% 0.20/0.47         (((k7_relat_1 @ X8 @ X7) = (k5_relat_1 @ (k6_relat_1 @ X7) @ X8))
% 0.20/0.47          | ~ (v1_relat_1 @ X8))),
% 0.20/0.47      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.47            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.47  thf('16', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.20/0.47           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('19', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('20', plain, (![X9 : $i]: (v1_relat_1 @ (k6_relat_1 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.20/0.47            = (k1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '17', '18', '19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.20/0.47            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X1)
% 0.20/0.47          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.20/0.47              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf(t70_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.20/0.47         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X13 @ (k1_relat_1 @ (k7_relat_1 @ X14 @ X15)))
% 0.20/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X14 @ X15) @ X13)
% 0.20/0.47              = (k1_funct_1 @ X14 @ X13))
% 0.20/0.47          | ~ (v1_funct_1 @ X14)
% 0.20/0.47          | ~ (v1_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (v1_funct_1 @ X1)
% 0.20/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.47              = (k1_funct_1 @ X1 @ X2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_funct_1 @ X1 @ X2))
% 0.20/0.47          | ~ (v1_funct_1 @ X1)
% 0.20/0.47          | ~ (v1_relat_1 @ X1)
% 0.20/0.47          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_relat_1 @ X0)))
% 0.20/0.47          | ~ (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_funct_1 @ X0)
% 0.20/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ X1) @ X2)
% 0.20/0.47              = (k1_funct_1 @ X0 @ X2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.47          = (k1_funct_1 @ sk_C @ sk_A))
% 0.20/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '27'])).
% 0.20/0.47  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.47         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.47         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
