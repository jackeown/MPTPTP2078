%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2F33nlypJU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:47 EST 2020

% Result     : Theorem 3.66s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   49 (  70 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  451 ( 760 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X41 @ X42 ) @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X46 @ ( k1_relat_1 @ X47 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X47 @ X46 ) )
        = X46 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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

thf('4',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X37 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X37 @ X36 ) @ X35 )
        = ( k7_relat_1 @ X37 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X30 @ X31 ) @ X32 )
        = ( k7_relat_1 @ X30 @ ( k3_xboole_0 @ X31 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X50 @ X49 ) @ X51 )
        = ( k3_xboole_0 @ X49 @ ( k10_relat_1 @ X50 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) ) )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2F33nlypJU
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.66/3.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.66/3.90  % Solved by: fo/fo7.sh
% 3.66/3.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.66/3.90  % done 4035 iterations in 3.449s
% 3.66/3.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.66/3.90  % SZS output start Refutation
% 3.66/3.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.66/3.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.66/3.90  thf(sk_C_type, type, sk_C: $i).
% 3.66/3.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.66/3.90  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.66/3.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.66/3.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.66/3.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.66/3.90  thf(sk_B_type, type, sk_B: $i).
% 3.66/3.90  thf(sk_A_type, type, sk_A: $i).
% 3.66/3.90  thf(t167_relat_1, axiom,
% 3.66/3.90    (![A:$i,B:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ B ) =>
% 3.66/3.90       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 3.66/3.90  thf('0', plain,
% 3.66/3.90      (![X41 : $i, X42 : $i]:
% 3.66/3.90         ((r1_tarski @ (k10_relat_1 @ X41 @ X42) @ (k1_relat_1 @ X41))
% 3.66/3.90          | ~ (v1_relat_1 @ X41))),
% 3.66/3.90      inference('cnf', [status(esa)], [t167_relat_1])).
% 3.66/3.90  thf(t91_relat_1, axiom,
% 3.66/3.90    (![A:$i,B:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ B ) =>
% 3.66/3.90       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.66/3.90         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.66/3.90  thf('1', plain,
% 3.66/3.90      (![X46 : $i, X47 : $i]:
% 3.66/3.90         (~ (r1_tarski @ X46 @ (k1_relat_1 @ X47))
% 3.66/3.90          | ((k1_relat_1 @ (k7_relat_1 @ X47 @ X46)) = (X46))
% 3.66/3.90          | ~ (v1_relat_1 @ X47))),
% 3.66/3.90      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.66/3.90  thf('2', plain,
% 3.66/3.90      (![X0 : $i, X1 : $i]:
% 3.66/3.90         (~ (v1_relat_1 @ X0)
% 3.66/3.90          | ~ (v1_relat_1 @ X0)
% 3.66/3.90          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 3.66/3.90              = (k10_relat_1 @ X0 @ X1)))),
% 3.66/3.90      inference('sup-', [status(thm)], ['0', '1'])).
% 3.66/3.90  thf('3', plain,
% 3.66/3.90      (![X0 : $i, X1 : $i]:
% 3.66/3.90         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 3.66/3.90            = (k10_relat_1 @ X0 @ X1))
% 3.66/3.90          | ~ (v1_relat_1 @ X0))),
% 3.66/3.90      inference('simplify', [status(thm)], ['2'])).
% 3.66/3.90  thf(t175_funct_2, conjecture,
% 3.66/3.90    (![A:$i]:
% 3.66/3.90     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.66/3.90       ( ![B:$i,C:$i]:
% 3.66/3.90         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 3.66/3.90           ( ( k10_relat_1 @ A @ C ) =
% 3.66/3.90             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 3.66/3.90  thf(zf_stmt_0, negated_conjecture,
% 3.66/3.90    (~( ![A:$i]:
% 3.66/3.90        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.66/3.90          ( ![B:$i,C:$i]:
% 3.66/3.90            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 3.66/3.90              ( ( k10_relat_1 @ A @ C ) =
% 3.66/3.90                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 3.66/3.90    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 3.66/3.90  thf('4', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf(t103_relat_1, axiom,
% 3.66/3.90    (![A:$i,B:$i,C:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ C ) =>
% 3.66/3.90       ( ( r1_tarski @ A @ B ) =>
% 3.66/3.90         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 3.66/3.90  thf('5', plain,
% 3.66/3.90      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.66/3.90         (~ (r1_tarski @ X35 @ X36)
% 3.66/3.90          | ~ (v1_relat_1 @ X37)
% 3.66/3.90          | ((k7_relat_1 @ (k7_relat_1 @ X37 @ X36) @ X35)
% 3.66/3.90              = (k7_relat_1 @ X37 @ X35)))),
% 3.66/3.90      inference('cnf', [status(esa)], [t103_relat_1])).
% 3.66/3.90  thf('6', plain,
% 3.66/3.90      (![X0 : $i]:
% 3.66/3.90         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 3.66/3.90            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90          | ~ (v1_relat_1 @ X0))),
% 3.66/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.66/3.90  thf(dt_k7_relat_1, axiom,
% 3.66/3.90    (![A:$i,B:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.66/3.90  thf('7', plain,
% 3.66/3.90      (![X28 : $i, X29 : $i]:
% 3.66/3.90         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k7_relat_1 @ X28 @ X29)))),
% 3.66/3.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.66/3.90  thf('8', plain,
% 3.66/3.90      (![X0 : $i]:
% 3.66/3.90         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 3.66/3.90            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90          | ~ (v1_relat_1 @ X0))),
% 3.66/3.90      inference('sup-', [status(thm)], ['4', '5'])).
% 3.66/3.90  thf(t100_relat_1, axiom,
% 3.66/3.90    (![A:$i,B:$i,C:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ C ) =>
% 3.66/3.90       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.66/3.90         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 3.66/3.90  thf('9', plain,
% 3.66/3.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.66/3.90         (((k7_relat_1 @ (k7_relat_1 @ X30 @ X31) @ X32)
% 3.66/3.90            = (k7_relat_1 @ X30 @ (k3_xboole_0 @ X31 @ X32)))
% 3.66/3.90          | ~ (v1_relat_1 @ X30))),
% 3.66/3.90      inference('cnf', [status(esa)], [t100_relat_1])).
% 3.66/3.90  thf('10', plain,
% 3.66/3.90      (![X0 : $i]:
% 3.66/3.90         (((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 3.66/3.90            = (k7_relat_1 @ X0 @ 
% 3.66/3.90               (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 3.66/3.90          | ~ (v1_relat_1 @ X0)
% 3.66/3.90          | ~ (v1_relat_1 @ X0))),
% 3.66/3.90      inference('sup+', [status(thm)], ['8', '9'])).
% 3.66/3.90  thf('11', plain,
% 3.66/3.90      (![X0 : $i]:
% 3.66/3.90         (~ (v1_relat_1 @ X0)
% 3.66/3.90          | ((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 3.66/3.90              = (k7_relat_1 @ X0 @ 
% 3.66/3.90                 (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))))),
% 3.66/3.90      inference('simplify', [status(thm)], ['10'])).
% 3.66/3.90  thf(t139_funct_1, axiom,
% 3.66/3.90    (![A:$i,B:$i,C:$i]:
% 3.66/3.90     ( ( v1_relat_1 @ C ) =>
% 3.66/3.90       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 3.66/3.90         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 3.66/3.90  thf('12', plain,
% 3.66/3.90      (![X49 : $i, X50 : $i, X51 : $i]:
% 3.66/3.90         (((k10_relat_1 @ (k7_relat_1 @ X50 @ X49) @ X51)
% 3.66/3.90            = (k3_xboole_0 @ X49 @ (k10_relat_1 @ X50 @ X51)))
% 3.66/3.90          | ~ (v1_relat_1 @ X50))),
% 3.66/3.90      inference('cnf', [status(esa)], [t139_funct_1])).
% 3.66/3.90  thf('13', plain,
% 3.66/3.90      (![X0 : $i, X1 : $i]:
% 3.66/3.90         (((k1_relat_1 @ (k7_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1)))
% 3.66/3.90            = (k10_relat_1 @ X0 @ X1))
% 3.66/3.90          | ~ (v1_relat_1 @ X0))),
% 3.66/3.90      inference('simplify', [status(thm)], ['2'])).
% 3.66/3.90  thf('14', plain,
% 3.66/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.90         (((k1_relat_1 @ 
% 3.66/3.90            (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 3.66/3.90             (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))
% 3.66/3.90            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0))
% 3.66/3.90          | ~ (v1_relat_1 @ X1)
% 3.66/3.90          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X2)))),
% 3.66/3.90      inference('sup+', [status(thm)], ['12', '13'])).
% 3.66/3.90  thf('15', plain,
% 3.66/3.90      (![X28 : $i, X29 : $i]:
% 3.66/3.90         (~ (v1_relat_1 @ X28) | (v1_relat_1 @ (k7_relat_1 @ X28 @ X29)))),
% 3.66/3.90      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.66/3.90  thf('16', plain,
% 3.66/3.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.66/3.90         (~ (v1_relat_1 @ X1)
% 3.66/3.90          | ((k1_relat_1 @ 
% 3.66/3.90              (k7_relat_1 @ (k7_relat_1 @ X1 @ X2) @ 
% 3.66/3.90               (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))
% 3.66/3.90              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)))),
% 3.66/3.90      inference('clc', [status(thm)], ['14', '15'])).
% 3.66/3.90  thf('17', plain,
% 3.66/3.90      ((((k1_relat_1 @ 
% 3.66/3.90          (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 3.66/3.90           (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 3.66/3.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 3.66/3.90        | ~ (v1_relat_1 @ sk_A))),
% 3.66/3.90      inference('sup+', [status(thm)], ['11', '16'])).
% 3.66/3.90  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf('19', plain,
% 3.66/3.90      ((((k1_relat_1 @ 
% 3.66/3.90          (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 3.66/3.90           (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 3.66/3.90        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 3.66/3.90      inference('demod', [status(thm)], ['17', '18'])).
% 3.66/3.90  thf('20', plain,
% 3.66/3.90      ((~ (v1_relat_1 @ sk_A)
% 3.66/3.90        | ((k1_relat_1 @ 
% 3.66/3.90            (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 3.66/3.90             (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90            = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))),
% 3.66/3.90      inference('sup-', [status(thm)], ['7', '19'])).
% 3.66/3.90  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf('22', plain,
% 3.66/3.90      (((k1_relat_1 @ 
% 3.66/3.90         (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 3.66/3.90      inference('demod', [status(thm)], ['20', '21'])).
% 3.66/3.90  thf('23', plain,
% 3.66/3.90      ((((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 3.66/3.90        | ~ (v1_relat_1 @ sk_A))),
% 3.66/3.90      inference('sup+', [status(thm)], ['6', '22'])).
% 3.66/3.90  thf('24', plain, ((v1_relat_1 @ sk_A)),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf('25', plain,
% 3.66/3.90      (((k1_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)))
% 3.66/3.90         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 3.66/3.90      inference('demod', [status(thm)], ['23', '24'])).
% 3.66/3.90  thf('26', plain,
% 3.66/3.90      ((((k10_relat_1 @ sk_A @ sk_C)
% 3.66/3.90          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 3.66/3.90        | ~ (v1_relat_1 @ sk_A))),
% 3.66/3.90      inference('sup+', [status(thm)], ['3', '25'])).
% 3.66/3.90  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf('28', plain,
% 3.66/3.90      (((k10_relat_1 @ sk_A @ sk_C)
% 3.66/3.90         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 3.66/3.90      inference('demod', [status(thm)], ['26', '27'])).
% 3.66/3.90  thf('29', plain,
% 3.66/3.90      (((k10_relat_1 @ sk_A @ sk_C)
% 3.66/3.90         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 3.66/3.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.66/3.90  thf('30', plain, ($false),
% 3.66/3.90      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 3.66/3.90  
% 3.66/3.90  % SZS output end Refutation
% 3.66/3.91  
% 3.66/3.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
