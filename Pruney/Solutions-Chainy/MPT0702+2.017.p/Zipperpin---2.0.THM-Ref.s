%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCxn67LXfC

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:44 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   64 (  89 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   15
%              Number of atoms          :  412 ( 856 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( r1_tarski @ X15 @ ( k10_relat_1 @ X16 @ ( k9_relat_1 @ X16 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k10_relat_1 @ X7 @ X5 ) @ ( k10_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k10_relat_1 @ X0 @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('20',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X18 ) ) @ X18 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(t218_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v5_relat_1 @ C @ A ) )
         => ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ( v5_relat_1 @ X8 @ X10 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t218_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( v5_relat_1 @ X2 @ X0 )
      | ~ ( v5_relat_1 @ X2 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('31',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['29','30','31','32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('39',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rCxn67LXfC
% 0.16/0.39  % Computer   : n004.cluster.edu
% 0.16/0.39  % Model      : x86_64 x86_64
% 0.16/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.39  % Memory     : 8042.1875MB
% 0.16/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.39  % CPULimit   : 60
% 0.16/0.39  % DateTime   : Tue Dec  1 17:42:39 EST 2020
% 0.16/0.39  % CPUTime    : 
% 0.16/0.39  % Running portfolio for 600 s
% 0.16/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 81 iterations in 0.047s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.25/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.25/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.25/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.25/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.25/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.55  thf(t157_funct_1, conjecture,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.55       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.25/0.55           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.25/0.55         ( r1_tarski @ A @ B ) ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.55          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.25/0.55              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.25/0.55            ( r1_tarski @ A @ B ) ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.25/0.55  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t152_funct_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.25/0.55       ( ( v2_funct_1 @ B ) =>
% 0.25/0.55         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.25/0.55  thf('1', plain,
% 0.25/0.55      (![X17 : $i, X18 : $i]:
% 0.25/0.55         (~ (v2_funct_1 @ X17)
% 0.25/0.55          | (r1_tarski @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X18)) @ X18)
% 0.25/0.55          | ~ (v1_funct_1 @ X17)
% 0.25/0.55          | ~ (v1_relat_1 @ X17))),
% 0.25/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.25/0.55  thf('2', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t146_funct_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.25/0.55         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.25/0.55  thf('3', plain,
% 0.25/0.55      (![X15 : $i, X16 : $i]:
% 0.25/0.55         (~ (r1_tarski @ X15 @ (k1_relat_1 @ X16))
% 0.25/0.55          | (r1_tarski @ X15 @ (k10_relat_1 @ X16 @ (k9_relat_1 @ X16 @ X15)))
% 0.25/0.55          | ~ (v1_relat_1 @ X16))),
% 0.25/0.55      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.25/0.55  thf('4', plain,
% 0.25/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.25/0.55        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.25/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.55  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('6', plain,
% 0.25/0.55      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.25/0.55  thf(d10_xboole_0, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.25/0.55  thf('7', plain,
% 0.25/0.55      (![X0 : $i, X2 : $i]:
% 0.25/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.25/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.25/0.55  thf('8', plain,
% 0.25/0.55      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.25/0.55        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.25/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.25/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.25/0.55        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['1', '8'])).
% 0.25/0.55  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('12', plain, ((v2_funct_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('13', plain,
% 0.25/0.55      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.25/0.55  thf('14', plain,
% 0.25/0.55      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(t178_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ C ) =>
% 0.25/0.55       ( ( r1_tarski @ A @ B ) =>
% 0.25/0.55         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.25/0.55         (~ (r1_tarski @ X5 @ X6)
% 0.25/0.55          | ~ (v1_relat_1 @ X7)
% 0.25/0.55          | (r1_tarski @ (k10_relat_1 @ X7 @ X5) @ (k10_relat_1 @ X7 @ X6)))),
% 0.25/0.55      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.25/0.55  thf('16', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((r1_tarski @ (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.25/0.55           (k10_relat_1 @ X0 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.25/0.55          | ~ (v1_relat_1 @ X0))),
% 0.25/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.25/0.55  thf('17', plain,
% 0.25/0.55      (((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.25/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.25/0.55      inference('sup+', [status(thm)], ['13', '16'])).
% 0.25/0.55  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('19', plain,
% 0.25/0.55      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.25/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.25/0.55  thf(t71_relat_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.25/0.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.25/0.55  thf('20', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.25/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.25/0.55  thf(d19_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( v1_relat_1 @ B ) =>
% 0.25/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.25/0.55  thf('21', plain,
% 0.25/0.55      (![X3 : $i, X4 : $i]:
% 0.25/0.55         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.25/0.55          | (v5_relat_1 @ X3 @ X4)
% 0.25/0.55          | ~ (v1_relat_1 @ X3))),
% 0.25/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (r1_tarski @ X0 @ X1)
% 0.25/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.25/0.55          | (v5_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.25/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.25/0.55  thf(fc4_funct_1, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.25/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.25/0.55  thf('23', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.25/0.55  thf('24', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (~ (r1_tarski @ X0 @ X1) | (v5_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.25/0.55      inference('demod', [status(thm)], ['22', '23'])).
% 0.25/0.55  thf('25', plain,
% 0.25/0.55      ((v5_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.25/0.55        (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['19', '24'])).
% 0.25/0.55  thf('26', plain,
% 0.25/0.55      (![X17 : $i, X18 : $i]:
% 0.25/0.55         (~ (v2_funct_1 @ X17)
% 0.25/0.55          | (r1_tarski @ (k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X18)) @ X18)
% 0.25/0.55          | ~ (v1_funct_1 @ X17)
% 0.25/0.55          | ~ (v1_relat_1 @ X17))),
% 0.25/0.55      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.25/0.55  thf(t218_relat_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.25/0.55       ( ![C:$i]:
% 0.25/0.55         ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) ) =>
% 0.25/0.55           ( v5_relat_1 @ C @ B ) ) ) ))).
% 0.25/0.55  thf('27', plain,
% 0.25/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.55         (~ (v1_relat_1 @ X8)
% 0.25/0.55          | ~ (v5_relat_1 @ X8 @ X9)
% 0.25/0.55          | (v5_relat_1 @ X8 @ X10)
% 0.25/0.55          | ~ (r1_tarski @ X9 @ X10))),
% 0.25/0.55      inference('cnf', [status(esa)], [t218_relat_1])).
% 0.25/0.55  thf('28', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.55         (~ (v1_relat_1 @ X1)
% 0.25/0.55          | ~ (v1_funct_1 @ X1)
% 0.25/0.55          | ~ (v2_funct_1 @ X1)
% 0.25/0.55          | (v5_relat_1 @ X2 @ X0)
% 0.25/0.55          | ~ (v5_relat_1 @ X2 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.25/0.55          | ~ (v1_relat_1 @ X2))),
% 0.25/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.25/0.55  thf('29', plain,
% 0.25/0.55      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.25/0.55        | (v5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.25/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.25/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.25/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.25/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.25/0.55  thf('30', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.25/0.55  thf('31', plain, ((v2_funct_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('34', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)),
% 0.25/0.55      inference('demod', [status(thm)], ['29', '30', '31', '32', '33'])).
% 0.25/0.55  thf('35', plain,
% 0.25/0.55      (![X3 : $i, X4 : $i]:
% 0.25/0.55         (~ (v5_relat_1 @ X3 @ X4)
% 0.25/0.55          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 0.25/0.55          | ~ (v1_relat_1 @ X3))),
% 0.25/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.25/0.55  thf('36', plain,
% 0.25/0.55      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.25/0.55        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_A)) @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.25/0.55  thf('37', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.25/0.55  thf('38', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.25/0.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.25/0.55  thf('39', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.25/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.25/0.55  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.25/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
