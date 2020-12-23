%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KaqJLZ8Xp5

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:48 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  433 ( 535 expanded)
%              Number of equality atoms :   39 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
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
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ k1_xboole_0 )
    = ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k7_relat_1 @ X46 @ X45 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X39 @ X38 ) @ X40 )
        = ( k10_relat_1 @ X39 @ ( k10_relat_1 @ X38 @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ ( k6_relat_1 @ X49 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X50 ) @ ( k6_relat_1 @ X49 ) )
      = ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X49 @ X50 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X42 @ X41 ) )
        = ( k10_relat_1 @ X42 @ ( k1_relat_1 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k6_relat_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X43: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X47: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ ( k10_relat_1 @ X1 @ X2 ) @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KaqJLZ8Xp5
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.58  % Solved by: fo/fo7.sh
% 0.36/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.58  % done 281 iterations in 0.123s
% 0.36/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.58  % SZS output start Refutation
% 0.36/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.36/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.58  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.36/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.58  thf(t175_funct_2, conjecture,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.58       ( ![B:$i,C:$i]:
% 0.36/0.58         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.36/0.58           ( ( k10_relat_1 @ A @ C ) =
% 0.36/0.58             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.36/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.58    (~( ![A:$i]:
% 0.36/0.58        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.58          ( ![B:$i,C:$i]:
% 0.36/0.58            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.36/0.58              ( ( k10_relat_1 @ A @ C ) =
% 0.36/0.58                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.36/0.58    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.36/0.58  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf(l32_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.58  thf('1', plain,
% 0.36/0.58      (![X0 : $i, X2 : $i]:
% 0.36/0.58         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.58      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.58  thf('2', plain,
% 0.36/0.58      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B) = (k1_xboole_0))),
% 0.36/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.58  thf(t48_xboole_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.58  thf('3', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.36/0.58           = (k3_xboole_0 @ X7 @ X8))),
% 0.36/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.58  thf(t12_setfam_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.58  thf('4', plain,
% 0.36/0.58      (![X36 : $i, X37 : $i]:
% 0.36/0.58         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.58  thf('5', plain,
% 0.36/0.58      (![X7 : $i, X8 : $i]:
% 0.36/0.58         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.36/0.58           = (k1_setfam_1 @ (k2_tarski @ X7 @ X8)))),
% 0.36/0.58      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.58  thf('6', plain,
% 0.36/0.58      (((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ k1_xboole_0)
% 0.36/0.58         = (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['2', '5'])).
% 0.36/0.58  thf(t3_boole, axiom,
% 0.36/0.58    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.58  thf('7', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.36/0.58      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.58  thf('8', plain,
% 0.36/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.58         = (k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)))),
% 0.36/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.58  thf(t94_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ B ) =>
% 0.36/0.58       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.36/0.58  thf('9', plain,
% 0.36/0.58      (![X45 : $i, X46 : $i]:
% 0.36/0.58         (((k7_relat_1 @ X46 @ X45) = (k5_relat_1 @ (k6_relat_1 @ X45) @ X46))
% 0.36/0.58          | ~ (v1_relat_1 @ X46))),
% 0.36/0.58      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.36/0.58  thf(t181_relat_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ B ) =>
% 0.36/0.58       ( ![C:$i]:
% 0.36/0.58         ( ( v1_relat_1 @ C ) =>
% 0.36/0.58           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.36/0.58             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.36/0.58  thf('10', plain,
% 0.36/0.58      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X38)
% 0.36/0.58          | ((k10_relat_1 @ (k5_relat_1 @ X39 @ X38) @ X40)
% 0.36/0.58              = (k10_relat_1 @ X39 @ (k10_relat_1 @ X38 @ X40)))
% 0.36/0.58          | ~ (v1_relat_1 @ X39))),
% 0.36/0.58      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.36/0.58  thf(t43_funct_1, axiom,
% 0.36/0.58    (![A:$i,B:$i]:
% 0.36/0.58     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.36/0.58       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.58  thf('11', plain,
% 0.36/0.58      (![X49 : $i, X50 : $i]:
% 0.36/0.58         ((k5_relat_1 @ (k6_relat_1 @ X50) @ (k6_relat_1 @ X49))
% 0.36/0.58           = (k6_relat_1 @ (k3_xboole_0 @ X49 @ X50)))),
% 0.36/0.58      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.36/0.58  thf('12', plain,
% 0.36/0.58      (![X36 : $i, X37 : $i]:
% 0.36/0.58         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.36/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.36/0.58  thf('13', plain,
% 0.36/0.58      (![X49 : $i, X50 : $i]:
% 0.36/0.58         ((k5_relat_1 @ (k6_relat_1 @ X50) @ (k6_relat_1 @ X49))
% 0.36/0.58           = (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X49 @ X50))))),
% 0.36/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.36/0.58  thf(t71_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.36/0.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.36/0.58  thf('14', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.58  thf(t182_relat_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_relat_1 @ A ) =>
% 0.36/0.58       ( ![B:$i]:
% 0.36/0.58         ( ( v1_relat_1 @ B ) =>
% 0.36/0.58           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.36/0.58             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.36/0.58  thf('15', plain,
% 0.36/0.58      (![X41 : $i, X42 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X41)
% 0.36/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X42 @ X41))
% 0.36/0.58              = (k10_relat_1 @ X42 @ (k1_relat_1 @ X41)))
% 0.36/0.58          | ~ (v1_relat_1 @ X42))),
% 0.36/0.58      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.36/0.58  thf('16', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.36/0.58            = (k10_relat_1 @ X1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.58  thf(fc3_funct_1, axiom,
% 0.36/0.58    (![A:$i]:
% 0.36/0.58     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.36/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.36/0.58  thf('17', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.58  thf('18', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.36/0.58            = (k10_relat_1 @ X1 @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.58  thf('19', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         (((k1_relat_1 @ (k6_relat_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 0.36/0.58            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.36/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.36/0.58      inference('sup+', [status(thm)], ['13', '18'])).
% 0.36/0.58  thf('20', plain, (![X43 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X43)) = (X43))),
% 0.36/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.36/0.58  thf('21', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.58  thf('22', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i]:
% 0.36/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.36/0.58           = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.58  thf('23', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.36/0.58            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['10', '22'])).
% 0.36/0.58  thf('24', plain, (![X47 : $i]: (v1_relat_1 @ (k6_relat_1 @ X47))),
% 0.36/0.58      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.58  thf('25', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X0) @ X2))
% 0.36/0.58            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('demod', [status(thm)], ['23', '24'])).
% 0.36/0.58  thf('26', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.36/0.58            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.36/0.58          | ~ (v1_relat_1 @ X1)
% 0.36/0.58          | ~ (v1_relat_1 @ X1))),
% 0.36/0.58      inference('sup+', [status(thm)], ['9', '25'])).
% 0.36/0.58  thf('27', plain,
% 0.36/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.58         (~ (v1_relat_1 @ X1)
% 0.36/0.58          | ((k1_setfam_1 @ (k2_tarski @ (k10_relat_1 @ X1 @ X2) @ X0))
% 0.36/0.58              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.36/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.58  thf('28', plain,
% 0.36/0.58      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.58          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.36/0.58        | ~ (v1_relat_1 @ sk_A))),
% 0.36/0.58      inference('sup+', [status(thm)], ['8', '27'])).
% 0.36/0.58  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('30', plain,
% 0.36/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.58         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.36/0.58      inference('demod', [status(thm)], ['28', '29'])).
% 0.36/0.58  thf('31', plain,
% 0.36/0.58      (((k10_relat_1 @ sk_A @ sk_C)
% 0.36/0.58         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.36/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.58  thf('32', plain, ($false),
% 0.36/0.58      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.36/0.58  
% 0.36/0.58  % SZS output end Refutation
% 0.36/0.58  
% 0.36/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
