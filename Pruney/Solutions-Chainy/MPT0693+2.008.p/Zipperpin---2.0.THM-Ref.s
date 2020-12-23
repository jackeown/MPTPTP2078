%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SIPtt0mn8m

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:31 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  411 ( 586 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X40 @ X41 )
        = ( k10_relat_1 @ X40 @ ( k3_xboole_0 @ ( k2_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('2',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ X40 @ X41 )
        = ( k10_relat_1 @ X40 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X40 ) @ X41 ) ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) @ X5 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k2_relat_1 @ X44 ) )
      | ( ( k9_relat_1 @ X44 @ ( k10_relat_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X42: $i] :
      ( ( ( k10_relat_1 @ X42 @ ( k2_relat_1 @ X42 ) )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r1_tarski @ X43 @ ( k2_relat_1 @ X44 ) )
      | ( ( k9_relat_1 @ X44 @ ( k10_relat_1 @ X44 @ X43 ) )
        = X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t148_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_funct_1])).

thf('17',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k9_relat_1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ( k9_relat_1 @ sk_B @ ( k10_relat_1 @ sk_B @ sk_A ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
     != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(simplify,[status(thm)],['31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.09  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SIPtt0mn8m
% 0.09/0.29  % Computer   : n010.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 20:19:59 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running portfolio for 600 s
% 0.09/0.29  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.09/0.29  % Number of cores: 8
% 0.09/0.29  % Python version: Python 3.6.8
% 0.09/0.29  % Running in FO mode
% 0.13/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.13/0.52  % Solved by: fo/fo7.sh
% 0.13/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.13/0.52  % done 246 iterations in 0.145s
% 0.13/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.13/0.52  % SZS output start Refutation
% 0.13/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.13/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.13/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.13/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.13/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.13/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.13/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.13/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.13/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.13/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.13/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.13/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.13/0.52  thf(t168_relat_1, axiom,
% 0.13/0.52    (![A:$i,B:$i]:
% 0.13/0.52     ( ( v1_relat_1 @ B ) =>
% 0.13/0.52       ( ( k10_relat_1 @ B @ A ) =
% 0.13/0.52         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.13/0.52  thf('0', plain,
% 0.13/0.52      (![X40 : $i, X41 : $i]:
% 0.13/0.52         (((k10_relat_1 @ X40 @ X41)
% 0.13/0.52            = (k10_relat_1 @ X40 @ (k3_xboole_0 @ (k2_relat_1 @ X40) @ X41)))
% 0.13/0.52          | ~ (v1_relat_1 @ X40))),
% 0.13/0.52      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.13/0.52  thf(t12_setfam_1, axiom,
% 0.13/0.52    (![A:$i,B:$i]:
% 0.13/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.13/0.52  thf('1', plain,
% 0.13/0.52      (![X38 : $i, X39 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.13/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.13/0.52  thf('2', plain,
% 0.13/0.52      (![X40 : $i, X41 : $i]:
% 0.13/0.52         (((k10_relat_1 @ X40 @ X41)
% 0.13/0.52            = (k10_relat_1 @ X40 @ 
% 0.13/0.52               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X40) @ X41))))
% 0.13/0.52          | ~ (v1_relat_1 @ X40))),
% 0.13/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.13/0.52  thf(t17_xboole_1, axiom,
% 0.13/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.13/0.52  thf('3', plain,
% 0.13/0.52      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 0.13/0.52      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.13/0.52  thf('4', plain,
% 0.13/0.52      (![X38 : $i, X39 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.13/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.13/0.52  thf('5', plain,
% 0.13/0.52      (![X5 : $i, X6 : $i]:
% 0.13/0.52         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X5 @ X6)) @ X5)),
% 0.13/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.13/0.52  thf(t147_funct_1, axiom,
% 0.13/0.52    (![A:$i,B:$i]:
% 0.13/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.13/0.52       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.13/0.52         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.13/0.52  thf('6', plain,
% 0.13/0.52      (![X43 : $i, X44 : $i]:
% 0.13/0.52         (~ (r1_tarski @ X43 @ (k2_relat_1 @ X44))
% 0.13/0.52          | ((k9_relat_1 @ X44 @ (k10_relat_1 @ X44 @ X43)) = (X43))
% 0.13/0.52          | ~ (v1_funct_1 @ X44)
% 0.13/0.52          | ~ (v1_relat_1 @ X44))),
% 0.13/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.13/0.52  thf('7', plain,
% 0.13/0.52      (![X0 : $i, X1 : $i]:
% 0.13/0.52         (~ (v1_relat_1 @ X0)
% 0.13/0.52          | ~ (v1_funct_1 @ X0)
% 0.13/0.52          | ((k9_relat_1 @ X0 @ 
% 0.13/0.52              (k10_relat_1 @ X0 @ 
% 0.13/0.52               (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X1))))
% 0.13/0.52              = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X0) @ X1))))),
% 0.13/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.13/0.52  thf('8', plain,
% 0.13/0.52      (![X0 : $i, X1 : $i]:
% 0.13/0.52         (((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.13/0.52            = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ X0)))
% 0.13/0.52          | ~ (v1_relat_1 @ X1)
% 0.13/0.52          | ~ (v1_funct_1 @ X1)
% 0.13/0.52          | ~ (v1_relat_1 @ X1))),
% 0.13/0.52      inference('sup+', [status(thm)], ['2', '7'])).
% 0.13/0.52  thf('9', plain,
% 0.13/0.52      (![X0 : $i, X1 : $i]:
% 0.13/0.52         (~ (v1_funct_1 @ X1)
% 0.13/0.52          | ~ (v1_relat_1 @ X1)
% 0.13/0.52          | ((k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0))
% 0.13/0.52              = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X1) @ X0))))),
% 0.13/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.13/0.52  thf(t169_relat_1, axiom,
% 0.13/0.52    (![A:$i]:
% 0.13/0.52     ( ( v1_relat_1 @ A ) =>
% 0.13/0.52       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.13/0.52  thf('10', plain,
% 0.13/0.52      (![X42 : $i]:
% 0.13/0.52         (((k10_relat_1 @ X42 @ (k2_relat_1 @ X42)) = (k1_relat_1 @ X42))
% 0.13/0.52          | ~ (v1_relat_1 @ X42))),
% 0.13/0.52      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.13/0.52  thf(d10_xboole_0, axiom,
% 0.13/0.52    (![A:$i,B:$i]:
% 0.13/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.13/0.52  thf('11', plain,
% 0.13/0.52      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.13/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.13/0.52  thf('12', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.13/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.13/0.52  thf('13', plain,
% 0.13/0.52      (![X43 : $i, X44 : $i]:
% 0.13/0.52         (~ (r1_tarski @ X43 @ (k2_relat_1 @ X44))
% 0.13/0.52          | ((k9_relat_1 @ X44 @ (k10_relat_1 @ X44 @ X43)) = (X43))
% 0.13/0.52          | ~ (v1_funct_1 @ X44)
% 0.13/0.52          | ~ (v1_relat_1 @ X44))),
% 0.13/0.52      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.13/0.52  thf('14', plain,
% 0.13/0.52      (![X0 : $i]:
% 0.13/0.52         (~ (v1_relat_1 @ X0)
% 0.13/0.52          | ~ (v1_funct_1 @ X0)
% 0.13/0.52          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 0.13/0.52              = (k2_relat_1 @ X0)))),
% 0.13/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.13/0.52  thf('15', plain,
% 0.13/0.52      (![X0 : $i]:
% 0.13/0.52         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.13/0.52          | ~ (v1_relat_1 @ X0)
% 0.13/0.52          | ~ (v1_funct_1 @ X0)
% 0.13/0.52          | ~ (v1_relat_1 @ X0))),
% 0.13/0.52      inference('sup+', [status(thm)], ['10', '14'])).
% 0.13/0.52  thf('16', plain,
% 0.13/0.52      (![X0 : $i]:
% 0.13/0.52         (~ (v1_funct_1 @ X0)
% 0.13/0.52          | ~ (v1_relat_1 @ X0)
% 0.13/0.52          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.13/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.13/0.52  thf(t148_funct_1, conjecture,
% 0.13/0.52    (![A:$i,B:$i]:
% 0.13/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.13/0.52       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.13/0.52         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.13/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.13/0.52    (~( ![A:$i,B:$i]:
% 0.13/0.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.13/0.52          ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.13/0.52            ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )),
% 0.13/0.52    inference('cnf.neg', [status(esa)], [t148_funct_1])).
% 0.13/0.52  thf('17', plain,
% 0.13/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.13/0.52         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.13/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.52  thf('18', plain,
% 0.13/0.52      (![X38 : $i, X39 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.13/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.13/0.52  thf('19', plain,
% 0.13/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.13/0.52         != (k1_setfam_1 @ 
% 0.13/0.52             (k2_tarski @ sk_A @ (k9_relat_1 @ sk_B @ (k1_relat_1 @ sk_B)))))),
% 0.13/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.13/0.52  thf('20', plain,
% 0.13/0.52      ((((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.13/0.52          != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.13/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.13/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.13/0.52      inference('sup-', [status(thm)], ['16', '19'])).
% 0.13/0.52  thf('21', plain, ((v1_relat_1 @ sk_B)),
% 0.13/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.52  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.13/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.52  thf('23', plain,
% 0.13/0.52      (((k9_relat_1 @ sk_B @ (k10_relat_1 @ sk_B @ sk_A))
% 0.13/0.52         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.13/0.52      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.13/0.52  thf('24', plain,
% 0.13/0.52      ((((k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ sk_B) @ sk_A))
% 0.13/0.52          != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.13/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.13/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.13/0.52      inference('sup-', [status(thm)], ['9', '23'])).
% 0.13/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.13/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.13/0.52  thf('25', plain,
% 0.13/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.13/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.13/0.52  thf('26', plain,
% 0.13/0.52      (![X38 : $i, X39 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.13/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.13/0.52  thf('27', plain,
% 0.13/0.52      (![X38 : $i, X39 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 0.13/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.13/0.52  thf('28', plain,
% 0.13/0.52      (![X0 : $i, X1 : $i]:
% 0.13/0.52         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.13/0.52           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.13/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.13/0.52  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.13/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.52  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.13/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.13/0.52  thf('31', plain,
% 0.13/0.52      (((k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.13/0.52         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.13/0.52      inference('demod', [status(thm)], ['24', '28', '29', '30'])).
% 0.13/0.52  thf('32', plain, ($false), inference('simplify', [status(thm)], ['31'])).
% 0.13/0.52  
% 0.13/0.52  % SZS output end Refutation
% 0.13/0.52  
% 0.13/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
