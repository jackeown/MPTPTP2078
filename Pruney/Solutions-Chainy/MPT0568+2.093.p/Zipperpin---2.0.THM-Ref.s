%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1cixa53F10

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 (  94 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :  401 ( 540 expanded)
%              Number of equality atoms :   59 (  82 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X40 @ X41 )
        = ( k10_relat_1 @ X40 @ ( k3_xboole_0 @ ( k2_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X40 @ X41 )
        = ( k10_relat_1 @ X40 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X40 ) @ X41 ) ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X45: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X45 ) )
      = X45 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X43: $i] :
      ( ( ( k2_relat_1 @ X43 )
       != k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X39: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X42: $i] :
      ( ( ( k10_relat_1 @ X42 @ ( k2_relat_1 @ X42 ) )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('37',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('40',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','40'])).

thf('42',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1cixa53F10
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:24:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 47 iterations in 0.025s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(t172_relat_1, conjecture,
% 0.21/0.50    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.21/0.50  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t60_relat_1, axiom,
% 0.21/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf(t168_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( k10_relat_1 @ B @ A ) =
% 0.21/0.50         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X40 : $i, X41 : $i]:
% 0.21/0.50         (((k10_relat_1 @ X40 @ X41)
% 0.21/0.50            = (k10_relat_1 @ X40 @ (k3_xboole_0 @ (k2_relat_1 @ X40) @ X41)))
% 0.21/0.50          | ~ (v1_relat_1 @ X40))),
% 0.21/0.50      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.21/0.50  thf(t12_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X37 : $i, X38 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X40 : $i, X41 : $i]:
% 0.21/0.50         (((k10_relat_1 @ X40 @ X41)
% 0.21/0.50            = (k10_relat_1 @ X40 @ 
% 0.21/0.50               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X40) @ X41))))
% 0.21/0.50          | ~ (v1_relat_1 @ X40))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.50            = (k10_relat_1 @ k1_xboole_0 @ 
% 0.21/0.50               (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))
% 0.21/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('6', plain, (![X45 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X45)) = (X45))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(t64_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X43 : $i]:
% 0.21/0.50         (((k2_relat_1 @ X43) != (k1_xboole_0))
% 0.21/0.50          | ((X43) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ X43))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) != (k1_xboole_0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.50  thf('9', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.50  thf('12', plain, (![X39 : $i]: (v1_relat_1 @ (k6_relat_1 @ X39))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.50  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.50           = (k10_relat_1 @ k1_xboole_0 @ 
% 0.21/0.50              (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))))),
% 0.21/0.50      inference('demod', [status(thm)], ['5', '13'])).
% 0.21/0.50  thf(t100_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X37 : $i, X38 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf(t2_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X37 : $i, X38 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X4 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.50           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf(t5_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.50  thf('23', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.50  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf(t98_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ X8 @ X9)
% 0.21/0.50           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('27', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0))
% 0.21/0.50           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['17', '30'])).
% 0.21/0.50  thf(t4_boole, axiom,
% 0.21/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.21/0.50           = (k10_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '33'])).
% 0.21/0.50  thf('35', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf(t169_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X42 : $i]:
% 0.21/0.50         (((k10_relat_1 @ X42 @ (k2_relat_1 @ X42)) = (k1_relat_1 @ X42))
% 0.21/0.50          | ~ (v1_relat_1 @ X42))),
% 0.21/0.50      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.21/0.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.50  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.50      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '40'])).
% 0.21/0.50  thf('42', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '41'])).
% 0.21/0.50  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
