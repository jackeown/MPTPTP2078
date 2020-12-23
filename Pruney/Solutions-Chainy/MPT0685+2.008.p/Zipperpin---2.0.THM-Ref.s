%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.55ei4fjiVI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:08 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   68 (  90 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  509 ( 698 expanded)
%              Number of equality atoms :   45 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t181_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k10_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k10_relat_1 @ X18 @ ( k10_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t181_relat_1])).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X21 @ X20 ) )
        = ( k10_relat_1 @ X21 @ ( k1_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k7_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X24 ) @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('13',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k8_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ X15 @ ( k6_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X29 ) @ ( k6_relat_1 @ X28 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X14 @ X13 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X22: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k8_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['8','14','31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ X1 @ X2 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('40',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.55ei4fjiVI
% 0.13/0.37  % Computer   : n019.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:48:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.69/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.93  % Solved by: fo/fo7.sh
% 0.69/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.93  % done 367 iterations in 0.442s
% 0.69/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.93  % SZS output start Refutation
% 0.69/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.69/0.93  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.69/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.93  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.93  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.69/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.93  thf(t94_relat_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ B ) =>
% 0.69/0.93       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.69/0.93  thf('0', plain,
% 0.69/0.93      (![X24 : $i, X25 : $i]:
% 0.69/0.93         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 0.69/0.93          | ~ (v1_relat_1 @ X25))),
% 0.69/0.93      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.69/0.93  thf(t181_relat_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ B ) =>
% 0.69/0.93       ( ![C:$i]:
% 0.69/0.93         ( ( v1_relat_1 @ C ) =>
% 0.69/0.93           ( ( k10_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.69/0.93             ( k10_relat_1 @ B @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.69/0.93  thf('1', plain,
% 0.69/0.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.69/0.93         (~ (v1_relat_1 @ X17)
% 0.69/0.93          | ((k10_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 0.69/0.93              = (k10_relat_1 @ X18 @ (k10_relat_1 @ X17 @ X19)))
% 0.69/0.93          | ~ (v1_relat_1 @ X18))),
% 0.69/0.93      inference('cnf', [status(esa)], [t181_relat_1])).
% 0.69/0.93  thf('2', plain,
% 0.69/0.93      (![X24 : $i, X25 : $i]:
% 0.69/0.93         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 0.69/0.93          | ~ (v1_relat_1 @ X25))),
% 0.69/0.93      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.69/0.93  thf(t71_relat_1, axiom,
% 0.69/0.93    (![A:$i]:
% 0.69/0.93     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.69/0.93       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.69/0.93  thf('3', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.69/0.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.69/0.93  thf(t182_relat_1, axiom,
% 0.69/0.93    (![A:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ A ) =>
% 0.69/0.93       ( ![B:$i]:
% 0.69/0.93         ( ( v1_relat_1 @ B ) =>
% 0.69/0.93           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.69/0.93             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.69/0.93  thf('4', plain,
% 0.69/0.93      (![X20 : $i, X21 : $i]:
% 0.69/0.93         (~ (v1_relat_1 @ X20)
% 0.69/0.93          | ((k1_relat_1 @ (k5_relat_1 @ X21 @ X20))
% 0.69/0.93              = (k10_relat_1 @ X21 @ (k1_relat_1 @ X20)))
% 0.69/0.93          | ~ (v1_relat_1 @ X21))),
% 0.69/0.93      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.69/0.93  thf('5', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93            = (k10_relat_1 @ X1 @ X0))
% 0.69/0.93          | ~ (v1_relat_1 @ X1)
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['3', '4'])).
% 0.69/0.93  thf(fc3_funct_1, axiom,
% 0.69/0.93    (![A:$i]:
% 0.69/0.93     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.69/0.93       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.69/0.93  thf('6', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('7', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93            = (k10_relat_1 @ X1 @ X0))
% 0.69/0.93          | ~ (v1_relat_1 @ X1))),
% 0.69/0.93      inference('demod', [status(thm)], ['5', '6'])).
% 0.69/0.93  thf('8', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k1_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.69/0.93            = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['2', '7'])).
% 0.69/0.93  thf('9', plain,
% 0.69/0.93      (![X24 : $i, X25 : $i]:
% 0.69/0.93         (((k7_relat_1 @ X25 @ X24) = (k5_relat_1 @ (k6_relat_1 @ X24) @ X25))
% 0.69/0.93          | ~ (v1_relat_1 @ X25))),
% 0.69/0.93      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.69/0.93  thf(t123_relat_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ B ) =>
% 0.69/0.93       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.69/0.93  thf('10', plain,
% 0.69/0.93      (![X15 : $i, X16 : $i]:
% 0.69/0.93         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.69/0.93          | ~ (v1_relat_1 @ X15))),
% 0.69/0.93      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.69/0.93  thf('11', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.69/0.93            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['9', '10'])).
% 0.69/0.93  thf('12', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('13', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('14', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.69/0.93           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.69/0.93      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.69/0.93  thf('15', plain,
% 0.69/0.93      (![X15 : $i, X16 : $i]:
% 0.69/0.93         (((k8_relat_1 @ X16 @ X15) = (k5_relat_1 @ X15 @ (k6_relat_1 @ X16)))
% 0.69/0.93          | ~ (v1_relat_1 @ X15))),
% 0.69/0.93      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.69/0.93  thf(t43_funct_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.69/0.93       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.69/0.93  thf('16', plain,
% 0.69/0.93      (![X28 : $i, X29 : $i]:
% 0.69/0.93         ((k5_relat_1 @ (k6_relat_1 @ X29) @ (k6_relat_1 @ X28))
% 0.69/0.93           = (k6_relat_1 @ (k3_xboole_0 @ X28 @ X29)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.69/0.93  thf('17', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.69/0.93            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['15', '16'])).
% 0.69/0.93  thf('18', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('19', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.69/0.93           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.93      inference('demod', [status(thm)], ['17', '18'])).
% 0.69/0.93  thf('20', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.69/0.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.69/0.93  thf('21', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93           = (k3_xboole_0 @ X1 @ X0))),
% 0.69/0.93      inference('sup+', [status(thm)], ['19', '20'])).
% 0.69/0.93  thf('22', plain, (![X23 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 0.69/0.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.69/0.93  thf(t119_relat_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ B ) =>
% 0.69/0.93       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.69/0.93         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.69/0.93  thf('23', plain,
% 0.69/0.93      (![X13 : $i, X14 : $i]:
% 0.69/0.93         (((k2_relat_1 @ (k8_relat_1 @ X14 @ X13))
% 0.69/0.93            = (k3_xboole_0 @ (k2_relat_1 @ X13) @ X14))
% 0.69/0.93          | ~ (v1_relat_1 @ X13))),
% 0.69/0.93      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.69/0.93  thf('24', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93            = (k3_xboole_0 @ X0 @ X1))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['22', '23'])).
% 0.69/0.93  thf('25', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('26', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93           = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.93      inference('demod', [status(thm)], ['24', '25'])).
% 0.69/0.93  thf('27', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.93      inference('sup+', [status(thm)], ['21', '26'])).
% 0.69/0.93  thf('28', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k8_relat_1 @ X1 @ (k6_relat_1 @ X0))
% 0.69/0.93           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.93      inference('demod', [status(thm)], ['17', '18'])).
% 0.69/0.93  thf('29', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k8_relat_1 @ X0 @ (k6_relat_1 @ X1))
% 0.69/0.93           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['27', '28'])).
% 0.69/0.93  thf('30', plain, (![X22 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X22)) = (X22))),
% 0.69/0.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.69/0.93  thf('31', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k1_relat_1 @ (k8_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.69/0.93           = (k3_xboole_0 @ X0 @ X1))),
% 0.69/0.93      inference('sup+', [status(thm)], ['29', '30'])).
% 0.69/0.93  thf('32', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('33', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('34', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i]:
% 0.69/0.93         ((k3_xboole_0 @ X0 @ X1) = (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.69/0.93      inference('demod', [status(thm)], ['8', '14', '31', '32', '33'])).
% 0.69/0.93  thf('35', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.69/0.93            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.69/0.93          | ~ (v1_relat_1 @ (k6_relat_1 @ X2))
% 0.69/0.93          | ~ (v1_relat_1 @ X1))),
% 0.69/0.93      inference('sup+', [status(thm)], ['1', '34'])).
% 0.69/0.93  thf('36', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.69/0.93      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.69/0.93  thf('37', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))
% 0.69/0.93            = (k10_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X2) @ X1) @ X0))
% 0.69/0.93          | ~ (v1_relat_1 @ X1))),
% 0.69/0.93      inference('demod', [status(thm)], ['35', '36'])).
% 0.69/0.93  thf('38', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.69/0.93            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.69/0.93          | ~ (v1_relat_1 @ X1)
% 0.69/0.93          | ~ (v1_relat_1 @ X1))),
% 0.69/0.93      inference('sup+', [status(thm)], ['0', '37'])).
% 0.69/0.93  thf('39', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (~ (v1_relat_1 @ X1)
% 0.69/0.93          | ((k3_xboole_0 @ X0 @ (k10_relat_1 @ X1 @ X2))
% 0.69/0.93              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.69/0.93      inference('simplify', [status(thm)], ['38'])).
% 0.69/0.93  thf(t139_funct_1, conjecture,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( v1_relat_1 @ C ) =>
% 0.69/0.93       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.69/0.93         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.69/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.93        ( ( v1_relat_1 @ C ) =>
% 0.69/0.93          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.69/0.93            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.69/0.93    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 0.69/0.93  thf('40', plain,
% 0.69/0.93      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.69/0.93         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('41', plain,
% 0.69/0.93      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.69/0.93          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))
% 0.69/0.93        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.69/0.93  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('43', plain,
% 0.69/0.93      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.69/0.93         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B))),
% 0.69/0.93      inference('demod', [status(thm)], ['41', '42'])).
% 0.69/0.93  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.69/0.93  
% 0.69/0.93  % SZS output end Refutation
% 0.69/0.93  
% 0.76/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
