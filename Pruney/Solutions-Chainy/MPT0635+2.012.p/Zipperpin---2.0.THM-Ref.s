%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Art9nVhLaJ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:53 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 114 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  470 (1151 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k7_relat_1 @ X18 @ X17 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t21_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
          <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
              & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X23 ) ) )
      | ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t21_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k1_funct_1 @ X24 @ ( k1_funct_1 @ X25 @ X26 ) ) )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X28 ) @ X27 )
        = X27 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('30',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k1_funct_1 @ sk_C @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Art9nVhLaJ
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.90/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.08  % Solved by: fo/fo7.sh
% 0.90/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.08  % done 715 iterations in 0.633s
% 0.90/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.08  % SZS output start Refutation
% 0.90/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.08  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.08  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.90/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.08  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.90/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.08  thf(t90_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.90/1.08         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.08  thf('0', plain,
% 0.90/1.08      (![X15 : $i, X16 : $i]:
% 0.90/1.08         (((k1_relat_1 @ (k7_relat_1 @ X15 @ X16))
% 0.90/1.08            = (k3_xboole_0 @ (k1_relat_1 @ X15) @ X16))
% 0.90/1.08          | ~ (v1_relat_1 @ X15))),
% 0.90/1.08      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.90/1.08  thf(commutativity_k3_xboole_0, axiom,
% 0.90/1.08    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.90/1.08  thf('1', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.08  thf('2', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]:
% 0.90/1.08         (((k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))
% 0.90/1.08            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X1))),
% 0.90/1.08      inference('sup+', [status(thm)], ['0', '1'])).
% 0.90/1.08  thf(t38_funct_1, conjecture,
% 0.90/1.08    (![A:$i,B:$i,C:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.08       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.90/1.08         ( ( k1_funct_1 @ C @ A ) =
% 0.90/1.08           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.90/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.08    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.08        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.08          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.90/1.08            ( ( k1_funct_1 @ C @ A ) =
% 0.90/1.08              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.90/1.08    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.90/1.08  thf('3', plain,
% 0.90/1.08      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('4', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.90/1.08      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.90/1.08  thf('5', plain,
% 0.90/1.08      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.90/1.08      inference('demod', [status(thm)], ['3', '4'])).
% 0.90/1.08  thf('6', plain,
% 0.90/1.08      (((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.90/1.08        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.08      inference('sup+', [status(thm)], ['2', '5'])).
% 0.90/1.08  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('8', plain,
% 0.90/1.08      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.90/1.08      inference('demod', [status(thm)], ['6', '7'])).
% 0.90/1.08  thf(t94_relat_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( v1_relat_1 @ B ) =>
% 0.90/1.08       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.90/1.08  thf('9', plain,
% 0.90/1.08      (![X17 : $i, X18 : $i]:
% 0.90/1.08         (((k7_relat_1 @ X18 @ X17) = (k5_relat_1 @ (k6_relat_1 @ X17) @ X18))
% 0.90/1.08          | ~ (v1_relat_1 @ X18))),
% 0.90/1.08      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.90/1.08  thf(t21_funct_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.08       ( ![C:$i]:
% 0.90/1.08         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.08           ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) <=>
% 0.90/1.08             ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.90/1.08               ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.90/1.08  thf('10', plain,
% 0.90/1.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X21)
% 0.90/1.08          | ~ (v1_funct_1 @ X21)
% 0.90/1.08          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ (k5_relat_1 @ X21 @ X23)))
% 0.90/1.08          | (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.90/1.08          | ~ (v1_funct_1 @ X23)
% 0.90/1.08          | ~ (v1_relat_1 @ X23))),
% 0.90/1.08      inference('cnf', [status(esa)], [t21_funct_1])).
% 0.90/1.08  thf('11', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (v1_funct_1 @ X1)
% 0.90/1.08          | (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.90/1.08          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.90/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.90/1.08      inference('sup-', [status(thm)], ['9', '10'])).
% 0.90/1.08  thf(t71_relat_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.90/1.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.90/1.08  thf('12', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.08  thf(fc3_funct_1, axiom,
% 0.90/1.08    (![A:$i]:
% 0.90/1.08     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.90/1.08       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.90/1.08  thf('13', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.08  thf('14', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.08  thf('15', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (v1_funct_1 @ X1)
% 0.90/1.08          | (r2_hidden @ X2 @ X0))),
% 0.90/1.08      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.90/1.08  thf('16', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         ((r2_hidden @ X2 @ X0)
% 0.90/1.08          | ~ (v1_funct_1 @ X1)
% 0.90/1.08          | ~ (v1_relat_1 @ X1)
% 0.90/1.08          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.90/1.08      inference('simplify', [status(thm)], ['15'])).
% 0.90/1.08  thf('17', plain,
% 0.90/1.08      ((~ (v1_relat_1 @ sk_C)
% 0.90/1.08        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.08        | (r2_hidden @ sk_A @ sk_B))),
% 0.90/1.08      inference('sup-', [status(thm)], ['8', '16'])).
% 0.90/1.08  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.90/1.08  thf('21', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.90/1.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.90/1.08  thf(t23_funct_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.90/1.08       ( ![C:$i]:
% 0.90/1.08         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.90/1.08           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.90/1.08             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.90/1.08               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.90/1.08  thf('22', plain,
% 0.90/1.08      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X24)
% 0.90/1.08          | ~ (v1_funct_1 @ X24)
% 0.90/1.08          | ((k1_funct_1 @ (k5_relat_1 @ X25 @ X24) @ X26)
% 0.90/1.08              = (k1_funct_1 @ X24 @ (k1_funct_1 @ X25 @ X26)))
% 0.90/1.08          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X25))
% 0.90/1.08          | ~ (v1_funct_1 @ X25)
% 0.90/1.08          | ~ (v1_relat_1 @ X25))),
% 0.90/1.08      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.90/1.08  thf('23', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.90/1.08          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.90/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.90/1.08              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.90/1.08          | ~ (v1_funct_1 @ X2)
% 0.90/1.08          | ~ (v1_relat_1 @ X2))),
% 0.90/1.08      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.08  thf('24', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.08  thf('25', plain, (![X20 : $i]: (v1_funct_1 @ (k6_relat_1 @ X20))),
% 0.90/1.08      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.90/1.08  thf('26', plain,
% 0.90/1.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.08         (~ (r2_hidden @ X1 @ X0)
% 0.90/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.90/1.08              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.90/1.08          | ~ (v1_funct_1 @ X2)
% 0.90/1.08          | ~ (v1_relat_1 @ X2))),
% 0.90/1.08      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.90/1.08  thf('27', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (v1_funct_1 @ X0)
% 0.90/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.90/1.08              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.90/1.08      inference('sup-', [status(thm)], ['20', '26'])).
% 0.90/1.08  thf('28', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.90/1.08      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.90/1.08  thf(t35_funct_1, axiom,
% 0.90/1.08    (![A:$i,B:$i]:
% 0.90/1.08     ( ( r2_hidden @ A @ B ) =>
% 0.90/1.08       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.90/1.08  thf('29', plain,
% 0.90/1.08      (![X27 : $i, X28 : $i]:
% 0.90/1.08         (((k1_funct_1 @ (k6_relat_1 @ X28) @ X27) = (X27))
% 0.90/1.08          | ~ (r2_hidden @ X27 @ X28))),
% 0.90/1.08      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.90/1.08  thf('30', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.90/1.08      inference('sup-', [status(thm)], ['28', '29'])).
% 0.90/1.08  thf('31', plain,
% 0.90/1.08      (![X0 : $i]:
% 0.90/1.08         (~ (v1_relat_1 @ X0)
% 0.90/1.08          | ~ (v1_funct_1 @ X0)
% 0.90/1.08          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.90/1.08              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.90/1.08      inference('demod', [status(thm)], ['27', '30'])).
% 0.90/1.08  thf('32', plain,
% 0.90/1.08      (((k1_funct_1 @ sk_C @ sk_A)
% 0.90/1.08         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('33', plain,
% 0.90/1.08      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.90/1.08        | ~ (v1_funct_1 @ sk_C)
% 0.90/1.08        | ~ (v1_relat_1 @ sk_C))),
% 0.90/1.08      inference('sup-', [status(thm)], ['31', '32'])).
% 0.90/1.08  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.08  thf('36', plain,
% 0.90/1.08      (((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))),
% 0.90/1.08      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.90/1.08  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.90/1.08  
% 0.90/1.08  % SZS output end Refutation
% 0.90/1.08  
% 0.90/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
