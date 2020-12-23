%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q1NSy7hKTt

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  76 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :   18
%              Number of atoms          :  599 ( 691 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X29 @ X28 ) @ X30 )
        = ( k9_relat_1 @ X28 @ ( k9_relat_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('2',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k8_relat_1 @ X25 @ X24 )
        = ( k5_relat_1 @ X24 @ ( k6_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k9_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X32 @ X31 ) )
        = ( k9_relat_1 @ X31 @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X33: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X2 @ X0 ) ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_relat_1 @ X1 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
        = ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) )
        = ( k9_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X23 @ X22 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X22 ) @ X23 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X23 @ X22 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_relat_1 @ X22 ) @ X23 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k8_relat_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k8_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ X2 @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

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

thf('34',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k3_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('36',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k1_setfam_1 @ ( k2_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
     != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q1NSy7hKTt
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 109 iterations in 0.083s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.55  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(t123_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.21/0.55          | ~ (v1_relat_1 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.55  thf(t159_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ C ) =>
% 0.21/0.55           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.55             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X28)
% 0.21/0.55          | ((k9_relat_1 @ (k5_relat_1 @ X29 @ X28) @ X30)
% 0.21/0.55              = (k9_relat_1 @ X28 @ (k9_relat_1 @ X29 @ X30)))
% 0.21/0.55          | ~ (v1_relat_1 @ X29))),
% 0.21/0.55      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (((k8_relat_1 @ X25 @ X24) = (k5_relat_1 @ X24 @ (k6_relat_1 @ X25)))
% 0.21/0.55          | ~ (v1_relat_1 @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.55  thf(dt_k7_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.55  thf(t148_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X26 @ X27)) = (k9_relat_1 @ X26 @ X27))
% 0.21/0.55          | ~ (v1_relat_1 @ X26))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf(t160_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( v1_relat_1 @ B ) =>
% 0.21/0.55           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.55             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X31 : $i, X32 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X31)
% 0.21/0.55          | ((k2_relat_1 @ (k5_relat_1 @ X32 @ X31))
% 0.21/0.55              = (k9_relat_1 @ X31 @ (k2_relat_1 @ X32)))
% 0.21/0.55          | ~ (v1_relat_1 @ X32))),
% 0.21/0.55      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.55            = (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.55              = (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.55            = (k9_relat_1 @ X2 @ (k9_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55            = (k9_relat_1 @ (k6_relat_1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X2)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['2', '8'])).
% 0.21/0.55  thf(fc3_funct_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.55       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.55  thf('10', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55            = (k9_relat_1 @ (k6_relat_1 @ X2) @ (k9_relat_1 @ X1 @ X0)))
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55              = (k9_relat_1 @ (k6_relat_1 @ X2) @ (k9_relat_1 @ X1 @ X0))))),
% 0.21/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0)))
% 0.21/0.55            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '13'])).
% 0.21/0.55  thf('15', plain, (![X33 : $i]: (v1_relat_1 @ (k6_relat_1 @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0)))
% 0.21/0.55            = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ X2)
% 0.21/0.55          | ~ (v1_relat_1 @ X2))),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X2)
% 0.21/0.55          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k7_relat_1 @ X2 @ X0)))
% 0.21/0.55              = (k9_relat_1 @ (k5_relat_1 @ X2 @ (k6_relat_1 @ X1)) @ X0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2)))
% 0.21/0.55            = (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_relat_1 @ X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['0', '17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X0)
% 0.21/0.55          | ((k2_relat_1 @ (k8_relat_1 @ X1 @ (k7_relat_1 @ X0 @ X2)))
% 0.21/0.55              = (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k7_relat_1 @ X26 @ X27)) = (k9_relat_1 @ X26 @ X27))
% 0.21/0.55          | ~ (v1_relat_1 @ X26))),
% 0.21/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.55  thf(t119_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.55         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X23 @ X22))
% 0.21/0.55            = (k3_xboole_0 @ (k2_relat_1 @ X22) @ X23))
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.55  thf(t12_setfam_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X23 @ X22))
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ (k2_relat_1 @ X22) @ X23)))
% 0.21/0.55          | ~ (v1_relat_1 @ X22))),
% 0.21/0.55      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['20', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X20) | (v1_relat_1 @ (k7_relat_1 @ X20 @ X21)))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k2_relat_1 @ (k8_relat_1 @ X2 @ (k7_relat_1 @ X1 @ X0)))
% 0.21/0.55              = (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))))),
% 0.21/0.55      inference('clc', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 0.21/0.55          | ~ (v1_relat_1 @ X1)
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['19', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (v1_relat_1 @ X1)
% 0.21/0.55          | ((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.55              = (k1_setfam_1 @ (k2_tarski @ (k9_relat_1 @ X1 @ X0) @ X2))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.21/0.55           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (((k9_relat_1 @ (k8_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.55            = (k1_setfam_1 @ (k2_tarski @ X2 @ (k9_relat_1 @ X1 @ X0))))
% 0.21/0.55          | ~ (v1_relat_1 @ X1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['28', '32'])).
% 0.21/0.55  thf(t126_funct_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55       ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.55         ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.55          ( ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) =
% 0.21/0.55            ( k3_xboole_0 @ A @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t126_funct_1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.55         != (k3_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.55         != (k1_setfam_1 @ (k2_tarski @ sk_A @ (k9_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.55          != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.55      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.55  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (((k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.21/0.55         != (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
