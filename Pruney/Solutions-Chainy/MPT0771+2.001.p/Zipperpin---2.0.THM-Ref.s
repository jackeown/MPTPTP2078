%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kYXHSKoAkH

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:22 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   65 (  76 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  479 ( 631 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( ( k3_relat_1 @ X10 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_wellord1 @ X28 @ X27 )
        = ( k8_relat_1 @ X27 @ ( k7_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X15 @ X16 ) ) @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ X26 @ X25 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X25 @ X26 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 ) @ X0 )
      | ~ ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ ( k2_wellord1 @ X2 @ X0 ) ) @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t20_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
          & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_wellord1])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_wellord1 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k3_relat_1 @ X18 ) @ ( k3_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
   <= ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A )
    | ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['19','33'])).

thf('35',plain,(
    ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kYXHSKoAkH
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 214 iterations in 0.178s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.46/0.63  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(d6_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ( k3_relat_1 @ A ) =
% 0.46/0.63         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X10 : $i]:
% 0.46/0.63         (((k3_relat_1 @ X10)
% 0.46/0.63            = (k2_xboole_0 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.46/0.63          | ~ (v1_relat_1 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.46/0.63  thf(t18_wellord1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i]:
% 0.46/0.63         (((k2_wellord1 @ X28 @ X27)
% 0.46/0.63            = (k8_relat_1 @ X27 @ (k7_relat_1 @ X28 @ X27)))
% 0.46/0.63          | ~ (v1_relat_1 @ X28))),
% 0.46/0.63      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.46/0.63  thf(t116_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i]:
% 0.46/0.63         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X15 @ X16)) @ X15)
% 0.46/0.63          | ~ (v1_relat_1 @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['1', '2'])).
% 0.46/0.63  thf(dt_k7_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['3', '4'])).
% 0.46/0.63  thf(t17_wellord1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X25 : $i, X26 : $i]:
% 0.46/0.63         (((k2_wellord1 @ X26 @ X25)
% 0.46/0.63            = (k7_relat_1 @ (k8_relat_1 @ X25 @ X26) @ X25))
% 0.46/0.63          | ~ (v1_relat_1 @ X26))),
% 0.46/0.63      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.46/0.63  thf(t87_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      (![X19 : $i, X20 : $i]:
% 0.46/0.63         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X19 @ X20)) @ X20)
% 0.46/0.63          | ~ (v1_relat_1 @ X19))),
% 0.46/0.63      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ (k8_relat_1 @ X0 @ X1)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.63  thf(dt_k8_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X13 : $i, X14 : $i]:
% 0.46/0.63         ((v1_relat_1 @ (k8_relat_1 @ X13 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf(t8_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.46/0.63       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X2 @ X3)
% 0.46/0.63          | ~ (r1_tarski @ X4 @ X3)
% 0.46/0.63          | (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | (r1_tarski @ 
% 0.46/0.63             (k2_xboole_0 @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2) @ X0)
% 0.46/0.63          | ~ (r1_tarski @ X2 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | (r1_tarski @ 
% 0.46/0.63             (k2_xboole_0 @ (k1_relat_1 @ (k2_wellord1 @ X2 @ X0)) @ 
% 0.46/0.63              (k2_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ 
% 0.46/0.63             X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X2))),
% 0.46/0.63      inference('sup-', [status(thm)], ['5', '12'])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['0', '13'])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X1)
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0))
% 0.46/0.63          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.63  thf(dt_k2_wellord1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('clc', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf(t20_wellord1, conjecture,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ B ) =>
% 0.46/0.63       ( ( r1_tarski @
% 0.46/0.63           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.46/0.63         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i,B:$i]:
% 0.46/0.63        ( ( v1_relat_1 @ B ) =>
% 0.46/0.63          ( ( r1_tarski @
% 0.46/0.63              ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.46/0.63            ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t20_wellord1])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63           (k3_relat_1 @ sk_B))
% 0.46/0.63        | ~ (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A))
% 0.46/0.63         <= (~
% 0.46/0.63             ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A)))),
% 0.46/0.63      inference('split', [status(esa)], ['18'])).
% 0.46/0.63  thf(d6_wellord1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( k2_wellord1 @ A @ B ) =
% 0.46/0.63           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         (((k2_wellord1 @ X21 @ X22)
% 0.46/0.63            = (k3_xboole_0 @ X21 @ (k2_zfmisc_1 @ X22 @ X22)))
% 0.46/0.63          | ~ (v1_relat_1 @ X21))),
% 0.46/0.63      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.46/0.63  thf(t17_xboole_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.46/0.63      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.63  thf('22', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ X1) | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('sup+', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf(t31_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( v1_relat_1 @ B ) =>
% 0.46/0.63           ( ( r1_tarski @ A @ B ) =>
% 0.46/0.63             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X17)
% 0.46/0.63          | (r1_tarski @ (k3_relat_1 @ X18) @ (k3_relat_1 @ X17))
% 0.46/0.63          | ~ (r1_tarski @ X18 @ X17)
% 0.46/0.63          | ~ (v1_relat_1 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ X1))
% 0.46/0.63          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.46/0.63             (k3_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.63  thf('25', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.46/0.63           (k3_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ X1))
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ X1)) @ 
% 0.46/0.63             (k3_relat_1 @ X0)))),
% 0.46/0.63      inference('clc', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63           (k3_relat_1 @ sk_B)))
% 0.46/0.63         <= (~
% 0.46/0.63             ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63               (k3_relat_1 @ sk_B))))),
% 0.46/0.63      inference('split', [status(esa)], ['18'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_B))
% 0.46/0.63         <= (~
% 0.46/0.63             ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63               (k3_relat_1 @ sk_B))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63         (k3_relat_1 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (~ ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A)) | 
% 0.46/0.63       ~
% 0.46/0.63       ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ 
% 0.46/0.63         (k3_relat_1 @ sk_B)))),
% 0.46/0.63      inference('split', [status(esa)], ['18'])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (~ ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A))),
% 0.46/0.63      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.46/0.63  thf('34', plain,
% 0.46/0.63      (~ (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ sk_B @ sk_A)) @ sk_A)),
% 0.46/0.63      inference('simpl_trail', [status(thm)], ['19', '33'])).
% 0.46/0.63  thf('35', plain, (~ (v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '34'])).
% 0.46/0.63  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('37', plain, ($false), inference('demod', [status(thm)], ['35', '36'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.50/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
