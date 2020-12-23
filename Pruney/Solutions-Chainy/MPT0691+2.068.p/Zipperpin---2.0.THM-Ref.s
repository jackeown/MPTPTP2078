%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRXHvjWxgP

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:27 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  432 ( 789 expanded)
%              Number of equality atoms :   24 (  31 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X37 @ X36 ) @ X38 )
        = ( k3_xboole_0 @ X36 @ ( k10_relat_1 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) )
        = ( k9_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('8',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('9',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','23','24'])).

thf('26',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('30',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['10','11'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZRXHvjWxgP
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.08  % Solved by: fo/fo7.sh
% 0.83/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.08  % done 1200 iterations in 0.602s
% 0.83/1.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.08  % SZS output start Refutation
% 0.83/1.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.83/1.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.83/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.08  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.83/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.08  thf(t146_funct_1, conjecture,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.83/1.08         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.83/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.08    (~( ![A:$i,B:$i]:
% 0.83/1.08        ( ( v1_relat_1 @ B ) =>
% 0.83/1.08          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.83/1.08            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.83/1.08    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.83/1.08  thf('0', plain,
% 0.83/1.08      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(t139_funct_1, axiom,
% 0.83/1.08    (![A:$i,B:$i,C:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ C ) =>
% 0.83/1.08       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.83/1.08         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.83/1.08  thf('1', plain,
% 0.83/1.08      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.83/1.08         (((k10_relat_1 @ (k7_relat_1 @ X37 @ X36) @ X38)
% 0.83/1.08            = (k3_xboole_0 @ X36 @ (k10_relat_1 @ X37 @ X38)))
% 0.83/1.08          | ~ (v1_relat_1 @ X37))),
% 0.83/1.08      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.83/1.08  thf(t148_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.83/1.08  thf('2', plain,
% 0.83/1.08      (![X18 : $i, X19 : $i]:
% 0.83/1.08         (((k2_relat_1 @ (k7_relat_1 @ X18 @ X19)) = (k9_relat_1 @ X18 @ X19))
% 0.83/1.08          | ~ (v1_relat_1 @ X18))),
% 0.83/1.08      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.83/1.08  thf(t169_relat_1, axiom,
% 0.83/1.08    (![A:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ A ) =>
% 0.83/1.08       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.83/1.08  thf('3', plain,
% 0.83/1.08      (![X22 : $i]:
% 0.83/1.08         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.83/1.08          | ~ (v1_relat_1 @ X22))),
% 0.83/1.08      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.83/1.08  thf('4', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.83/1.08            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.83/1.08          | ~ (v1_relat_1 @ X1)
% 0.83/1.08          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.83/1.08      inference('sup+', [status(thm)], ['2', '3'])).
% 0.83/1.08  thf(dt_k7_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.83/1.08  thf('5', plain,
% 0.83/1.08      (![X16 : $i, X17 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.83/1.08      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.83/1.08  thf('6', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X1)
% 0.83/1.08          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.83/1.08              = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))),
% 0.83/1.08      inference('clc', [status(thm)], ['4', '5'])).
% 0.83/1.08  thf('7', plain,
% 0.83/1.08      (![X16 : $i, X17 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.83/1.08      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.83/1.08  thf('8', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf(t91_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.83/1.08         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.83/1.08  thf('9', plain,
% 0.83/1.08      (![X31 : $i, X32 : $i]:
% 0.83/1.08         (~ (r1_tarski @ X31 @ (k1_relat_1 @ X32))
% 0.83/1.08          | ((k1_relat_1 @ (k7_relat_1 @ X32 @ X31)) = (X31))
% 0.83/1.08          | ~ (v1_relat_1 @ X32))),
% 0.83/1.08      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.83/1.08  thf('10', plain,
% 0.83/1.08      ((~ (v1_relat_1 @ sk_B)
% 0.83/1.08        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.83/1.08      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.08  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('12', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.83/1.08  thf(t167_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.83/1.08  thf('13', plain,
% 0.83/1.08      (![X20 : $i, X21 : $i]:
% 0.83/1.08         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.83/1.08          | ~ (v1_relat_1 @ X20))),
% 0.83/1.08      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.83/1.08  thf('14', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.83/1.08          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('sup+', [status(thm)], ['12', '13'])).
% 0.83/1.08  thf('15', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ sk_B)
% 0.83/1.08          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.83/1.08      inference('sup-', [status(thm)], ['7', '14'])).
% 0.83/1.08  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('17', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.83/1.08      inference('demod', [status(thm)], ['15', '16'])).
% 0.83/1.08  thf(d10_xboole_0, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.83/1.08  thf('18', plain,
% 0.83/1.08      (![X0 : $i, X2 : $i]:
% 0.83/1.08         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.83/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.08  thf('19', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.83/1.08          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.83/1.08      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.08  thf('20', plain,
% 0.83/1.08      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.83/1.08        | ~ (v1_relat_1 @ sk_B)
% 0.83/1.08        | ((sk_A)
% 0.83/1.08            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.83/1.08               (k9_relat_1 @ sk_B @ sk_A))))),
% 0.83/1.08      inference('sup-', [status(thm)], ['6', '19'])).
% 0.83/1.08  thf('21', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.83/1.08  thf('22', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.83/1.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.83/1.08  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.83/1.08      inference('simplify', [status(thm)], ['22'])).
% 0.83/1.08  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('25', plain,
% 0.83/1.08      (((sk_A)
% 0.83/1.08         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.83/1.08            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('demod', [status(thm)], ['20', '21', '23', '24'])).
% 0.83/1.08  thf('26', plain,
% 0.83/1.08      ((((sk_A)
% 0.83/1.08          = (k3_xboole_0 @ sk_A @ 
% 0.83/1.08             (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))
% 0.83/1.08        | ~ (v1_relat_1 @ sk_B))),
% 0.83/1.08      inference('sup+', [status(thm)], ['1', '25'])).
% 0.83/1.08  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('28', plain,
% 0.83/1.08      (((sk_A)
% 0.83/1.08         = (k3_xboole_0 @ sk_A @ 
% 0.83/1.08            (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A))))),
% 0.83/1.08      inference('demod', [status(thm)], ['26', '27'])).
% 0.83/1.08  thf('29', plain,
% 0.83/1.08      (![X16 : $i, X17 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X16) | (v1_relat_1 @ (k7_relat_1 @ X16 @ X17)))),
% 0.83/1.08      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.83/1.08  thf('30', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.83/1.08      inference('demod', [status(thm)], ['10', '11'])).
% 0.83/1.08  thf(t90_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.83/1.08         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.83/1.08  thf('31', plain,
% 0.83/1.08      (![X29 : $i, X30 : $i]:
% 0.83/1.08         (((k1_relat_1 @ (k7_relat_1 @ X29 @ X30))
% 0.83/1.08            = (k3_xboole_0 @ (k1_relat_1 @ X29) @ X30))
% 0.83/1.08          | ~ (v1_relat_1 @ X29))),
% 0.83/1.08      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.83/1.08  thf(t87_relat_1, axiom,
% 0.83/1.08    (![A:$i,B:$i]:
% 0.83/1.08     ( ( v1_relat_1 @ B ) =>
% 0.83/1.08       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.83/1.08  thf('32', plain,
% 0.83/1.08      (![X27 : $i, X28 : $i]:
% 0.83/1.08         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X27 @ X28)) @ X28)
% 0.83/1.08          | ~ (v1_relat_1 @ X27))),
% 0.83/1.08      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.83/1.08  thf('33', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         ((r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0)
% 0.83/1.08          | ~ (v1_relat_1 @ X1)
% 0.83/1.08          | ~ (v1_relat_1 @ X1))),
% 0.83/1.08      inference('sup+', [status(thm)], ['31', '32'])).
% 0.83/1.08  thf('34', plain,
% 0.83/1.08      (![X0 : $i, X1 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ X1)
% 0.83/1.08          | (r1_tarski @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) @ X0))),
% 0.83/1.08      inference('simplify', [status(thm)], ['33'])).
% 0.83/1.08  thf('35', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         ((r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)
% 0.83/1.08          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('sup+', [status(thm)], ['30', '34'])).
% 0.83/1.08  thf('36', plain,
% 0.83/1.08      (![X0 : $i]:
% 0.83/1.08         (~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0))),
% 0.83/1.08      inference('sup-', [status(thm)], ['29', '35'])).
% 0.83/1.08  thf('37', plain, ((v1_relat_1 @ sk_B)),
% 0.83/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.08  thf('38', plain, (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ X0)),
% 0.83/1.08      inference('demod', [status(thm)], ['36', '37'])).
% 0.83/1.08  thf('39', plain,
% 0.83/1.08      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.83/1.08      inference('sup+', [status(thm)], ['28', '38'])).
% 0.83/1.08  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.83/1.08  
% 0.83/1.08  % SZS output end Refutation
% 0.83/1.08  
% 0.92/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
