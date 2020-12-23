%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lDdA7hY3RA

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  68 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  421 ( 481 expanded)
%              Number of equality atoms :   38 (  42 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X41 @ X40 ) @ X42 )
        = ( k9_relat_1 @ X40 @ ( k9_relat_1 @ X41 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X44: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X35 @ X34 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X34 ) @ X35 ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ X36 @ ( k6_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

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

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('12',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X0 @ X2 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf(t126_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t126_funct_1])).

thf('29',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lDdA7hY3RA
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:14:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 96 iterations in 0.065s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(t123_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (![X36 : $i, X37 : $i]:
% 0.22/0.53         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.22/0.53          | ~ (v1_relat_1 @ X36))),
% 0.22/0.53      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.53  thf(t159_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( v1_relat_1 @ C ) =>
% 0.22/0.53           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.22/0.53             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X40)
% 0.22/0.53          | ((k9_relat_1 @ (k5_relat_1 @ X41 @ X40) @ X42)
% 0.22/0.53              = (k9_relat_1 @ X40 @ (k9_relat_1 @ X41 @ X42)))
% 0.22/0.53          | ~ (v1_relat_1 @ X41))),
% 0.22/0.53      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.22/0.53  thf(t148_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X38 : $i, X39 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.22/0.53          | ~ (v1_relat_1 @ X38))),
% 0.22/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.53  thf(t71_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.53       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.53  thf('3', plain, (![X44 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X44)) = (X44))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.53  thf(t119_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.22/0.53         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X34 : $i, X35 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k8_relat_1 @ X35 @ X34))
% 0.22/0.53            = (k3_xboole_0 @ (k2_relat_1 @ X34) @ X35))
% 0.22/0.53          | ~ (v1_relat_1 @ X34))),
% 0.22/0.53      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.53            = (k3_xboole_0 @ X0 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.53  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.53  thf('6', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.53           = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X36 : $i, X37 : $i]:
% 0.22/0.53         (((k8_relat_1 @ X37 @ X36) = (k5_relat_1 @ X36 @ (k6_relat_1 @ X37)))
% 0.22/0.53          | ~ (v1_relat_1 @ X36))),
% 0.22/0.53      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.22/0.53  thf(t94_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X45 : $i, X46 : $i]:
% 0.22/0.53         (((k7_relat_1 @ X46 @ X45) = (k5_relat_1 @ (k6_relat_1 @ X45) @ X46))
% 0.22/0.53          | ~ (v1_relat_1 @ X46))),
% 0.22/0.53      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.53            = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('12', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.22/0.53           = (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.53           = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['7', '13'])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['2', '14'])).
% 0.22/0.53  thf('16', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k9_relat_1 @ (k6_relat_1 @ X1) @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.22/0.53            = (k3_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ X2)
% 0.22/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['1', '17'])).
% 0.22/0.53  thf('19', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)
% 0.22/0.53            = (k3_xboole_0 @ (k9_relat_1 @ X2 @ X0) @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ X2))),
% 0.22/0.53      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.53            = (k3_xboole_0 @ (k9_relat_1 @ X0 @ X2) @ X1))
% 0.22/0.53          | ~ (v1_relat_1 @ X0)
% 0.22/0.53          | ~ (v1_relat_1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['0', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ X0)
% 0.22/0.53          | ((k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.53              = (k3_xboole_0 @ (k9_relat_1 @ X0 @ X2) @ X1)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.53  thf(commutativity_k2_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.53  thf(t12_setfam_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X31 : $i, X32 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X31 : $i, X32 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X31 @ X32)) = (k3_xboole_0 @ X31 @ X32))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (((k3_xboole_0 @ X2 @ (k9_relat_1 @ X1 @ X0))
% 0.22/0.53            = (k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0))
% 0.22/0.53          | ~ (v1_relat_1 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['22', '27'])).
% 0.22/0.53  thf(t126_funct_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.22/0.53         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.53        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.53          ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.22/0.53            ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t126_funct_1])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.53         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.53          != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.22/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.53  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.22/0.53         != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.53  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
