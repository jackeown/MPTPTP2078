%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dTqGYEOnHO

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  591 ( 779 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( ( k8_relat_1 @ X20 @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X29 @ X31 ) @ X30 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X29 @ X30 ) @ X31 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('23',plain,(
    ! [X18: $i] :
      ( ( ( k3_relat_1 @ X18 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ X26 @ X25 )
        = ( k8_relat_1 @ X25 @ ( k7_relat_1 @ X26 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C @ sk_A ) )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dTqGYEOnHO
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.50/1.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.70  % Solved by: fo/fo7.sh
% 1.50/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.70  % done 506 iterations in 1.210s
% 1.50/1.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.70  % SZS output start Refutation
% 1.50/1.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.50/1.70  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 1.50/1.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.50/1.70  thf(sk_C_type, type, sk_C: $i).
% 1.50/1.70  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.50/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.50/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.50/1.70  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 1.50/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.70  thf(t29_wellord1, conjecture,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ C ) =>
% 1.50/1.70       ( ( r1_tarski @ A @ B ) =>
% 1.50/1.70         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.50/1.70           ( k2_wellord1 @ C @ A ) ) ) ))).
% 1.50/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.70    (~( ![A:$i,B:$i,C:$i]:
% 1.50/1.70        ( ( v1_relat_1 @ C ) =>
% 1.50/1.70          ( ( r1_tarski @ A @ B ) =>
% 1.50/1.70            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 1.50/1.70              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 1.50/1.70    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 1.50/1.70  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf(t20_wellord1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( r1_tarski @
% 1.50/1.70           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 1.50/1.70         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 1.50/1.70  thf('1', plain,
% 1.50/1.70      (![X27 : $i, X28 : $i]:
% 1.50/1.70         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X27 @ X28)) @ X28)
% 1.50/1.70          | ~ (v1_relat_1 @ X27))),
% 1.50/1.70      inference('cnf', [status(esa)], [t20_wellord1])).
% 1.50/1.70  thf(d6_relat_1, axiom,
% 1.50/1.70    (![A:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ A ) =>
% 1.50/1.70       ( ( k3_relat_1 @ A ) =
% 1.50/1.70         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.50/1.70  thf('2', plain,
% 1.50/1.70      (![X18 : $i]:
% 1.50/1.70         (((k3_relat_1 @ X18)
% 1.50/1.70            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.50/1.70          | ~ (v1_relat_1 @ X18))),
% 1.50/1.70      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.50/1.70  thf(d10_xboole_0, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.70  thf('3', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.50/1.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.70  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.50/1.70      inference('simplify', [status(thm)], ['3'])).
% 1.50/1.70  thf(t10_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.50/1.70  thf('5', plain,
% 1.50/1.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 1.50/1.70      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.50/1.70  thf('6', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['4', '5'])).
% 1.50/1.70  thf(t1_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.50/1.70       ( r1_tarski @ A @ C ) ))).
% 1.50/1.70  thf('7', plain,
% 1.50/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X6 @ X7)
% 1.50/1.70          | ~ (r1_tarski @ X7 @ X8)
% 1.50/1.70          | (r1_tarski @ X6 @ X8))),
% 1.50/1.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.50/1.70  thf('8', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.50/1.70      inference('sup-', [status(thm)], ['6', '7'])).
% 1.50/1.70  thf('9', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.50/1.70          | ~ (v1_relat_1 @ X0)
% 1.50/1.70          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['2', '8'])).
% 1.50/1.70  thf('10', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['1', '9'])).
% 1.50/1.70  thf(dt_k2_wellord1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 1.50/1.70  thf('11', plain,
% 1.50/1.70      (![X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.50/1.70  thf('12', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ X1))),
% 1.50/1.70      inference('clc', [status(thm)], ['10', '11'])).
% 1.50/1.70  thf('13', plain,
% 1.50/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X6 @ X7)
% 1.50/1.70          | ~ (r1_tarski @ X7 @ X8)
% 1.50/1.70          | (r1_tarski @ X6 @ X8))),
% 1.50/1.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.50/1.70  thf('14', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.70      inference('sup-', [status(thm)], ['12', '13'])).
% 1.50/1.70  thf('15', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.50/1.70          | ~ (v1_relat_1 @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['0', '14'])).
% 1.50/1.70  thf(t125_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.50/1.70         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 1.50/1.70  thf('16', plain,
% 1.50/1.70      (![X19 : $i, X20 : $i]:
% 1.50/1.70         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 1.50/1.70          | ((k8_relat_1 @ X20 @ X19) = (X19))
% 1.50/1.70          | ~ (v1_relat_1 @ X19))),
% 1.50/1.70      inference('cnf', [status(esa)], [t125_relat_1])).
% 1.50/1.70  thf('17', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['15', '16'])).
% 1.50/1.70  thf('18', plain,
% 1.50/1.70      (![X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.50/1.70  thf('19', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70            = (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70          | ~ (v1_relat_1 @ X0))),
% 1.50/1.70      inference('clc', [status(thm)], ['17', '18'])).
% 1.50/1.70  thf(t27_wellord1, axiom,
% 1.50/1.70    (![A:$i,B:$i,C:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ C ) =>
% 1.50/1.70       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 1.50/1.70         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 1.50/1.70  thf('20', plain,
% 1.50/1.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.50/1.70         (((k2_wellord1 @ (k2_wellord1 @ X29 @ X31) @ X30)
% 1.50/1.70            = (k2_wellord1 @ (k2_wellord1 @ X29 @ X30) @ X31))
% 1.50/1.70          | ~ (v1_relat_1 @ X29))),
% 1.50/1.70      inference('cnf', [status(esa)], [t27_wellord1])).
% 1.50/1.70  thf('21', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('22', plain,
% 1.50/1.70      (![X27 : $i, X28 : $i]:
% 1.50/1.70         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X27 @ X28)) @ X28)
% 1.50/1.70          | ~ (v1_relat_1 @ X27))),
% 1.50/1.70      inference('cnf', [status(esa)], [t20_wellord1])).
% 1.50/1.70  thf('23', plain,
% 1.50/1.70      (![X18 : $i]:
% 1.50/1.70         (((k3_relat_1 @ X18)
% 1.50/1.70            = (k2_xboole_0 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 1.50/1.70          | ~ (v1_relat_1 @ X18))),
% 1.50/1.70      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.50/1.70  thf(t7_xboole_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.50/1.70  thf('24', plain,
% 1.50/1.70      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 1.50/1.70      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.50/1.70  thf('25', plain,
% 1.50/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X6 @ X7)
% 1.50/1.70          | ~ (r1_tarski @ X7 @ X8)
% 1.50/1.70          | (r1_tarski @ X6 @ X8))),
% 1.50/1.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.50/1.70  thf('26', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.50/1.70      inference('sup-', [status(thm)], ['24', '25'])).
% 1.50/1.70  thf('27', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 1.50/1.70          | ~ (v1_relat_1 @ X0)
% 1.50/1.70          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.50/1.70      inference('sup-', [status(thm)], ['23', '26'])).
% 1.50/1.70  thf('28', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['22', '27'])).
% 1.50/1.70  thf('29', plain,
% 1.50/1.70      (![X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.50/1.70  thf('30', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i]:
% 1.50/1.70         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ X1))),
% 1.50/1.70      inference('clc', [status(thm)], ['28', '29'])).
% 1.50/1.70  thf('31', plain,
% 1.50/1.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.50/1.70         (~ (r1_tarski @ X6 @ X7)
% 1.50/1.70          | ~ (r1_tarski @ X7 @ X8)
% 1.50/1.70          | (r1_tarski @ X6 @ X8))),
% 1.50/1.70      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.50/1.70  thf('32', plain,
% 1.50/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X1)
% 1.50/1.70          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 1.50/1.70          | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.70      inference('sup-', [status(thm)], ['30', '31'])).
% 1.50/1.70  thf('33', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 1.50/1.70          | ~ (v1_relat_1 @ X0))),
% 1.50/1.70      inference('sup-', [status(thm)], ['21', '32'])).
% 1.50/1.70  thf(t97_relat_1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.50/1.70         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.50/1.70  thf('34', plain,
% 1.50/1.70      (![X21 : $i, X22 : $i]:
% 1.50/1.70         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 1.50/1.70          | ((k7_relat_1 @ X21 @ X22) = (X21))
% 1.50/1.70          | ~ (v1_relat_1 @ X21))),
% 1.50/1.70      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.50/1.70  thf('35', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.50/1.70              = (k2_wellord1 @ X0 @ sk_A)))),
% 1.50/1.70      inference('sup-', [status(thm)], ['33', '34'])).
% 1.50/1.70  thf('36', plain,
% 1.50/1.70      (![X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.50/1.70  thf('37', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.50/1.70            = (k2_wellord1 @ X0 @ sk_A))
% 1.50/1.70          | ~ (v1_relat_1 @ X0))),
% 1.50/1.70      inference('clc', [status(thm)], ['35', '36'])).
% 1.50/1.70  thf(t18_wellord1, axiom,
% 1.50/1.70    (![A:$i,B:$i]:
% 1.50/1.70     ( ( v1_relat_1 @ B ) =>
% 1.50/1.70       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 1.50/1.70  thf('38', plain,
% 1.50/1.70      (![X25 : $i, X26 : $i]:
% 1.50/1.70         (((k2_wellord1 @ X26 @ X25)
% 1.50/1.70            = (k8_relat_1 @ X25 @ (k7_relat_1 @ X26 @ X25)))
% 1.50/1.70          | ~ (v1_relat_1 @ X26))),
% 1.50/1.70      inference('cnf', [status(esa)], [t18_wellord1])).
% 1.50/1.70  thf('39', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.50/1.70            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.50/1.70          | ~ (v1_relat_1 @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 1.50/1.70      inference('sup+', [status(thm)], ['37', '38'])).
% 1.50/1.70  thf('40', plain,
% 1.50/1.70      (![X23 : $i, X24 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X23) | (v1_relat_1 @ (k2_wellord1 @ X23 @ X24)))),
% 1.50/1.70      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 1.50/1.70  thf('41', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X0)
% 1.50/1.70          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 1.50/1.70              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.50/1.70      inference('clc', [status(thm)], ['39', '40'])).
% 1.50/1.70  thf('42', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.50/1.70            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 1.50/1.70          | ~ (v1_relat_1 @ X0)
% 1.50/1.70          | ~ (v1_relat_1 @ X0))),
% 1.50/1.70      inference('sup+', [status(thm)], ['20', '41'])).
% 1.50/1.70  thf('43', plain,
% 1.50/1.70      (![X0 : $i]:
% 1.50/1.70         (~ (v1_relat_1 @ X0)
% 1.50/1.70          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 1.50/1.70              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 1.50/1.70      inference('simplify', [status(thm)], ['42'])).
% 1.50/1.70  thf('44', plain,
% 1.50/1.70      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 1.50/1.70         != (k2_wellord1 @ sk_C @ sk_A))),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('45', plain,
% 1.50/1.70      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 1.50/1.70          != (k2_wellord1 @ sk_C @ sk_A))
% 1.50/1.70        | ~ (v1_relat_1 @ sk_C))),
% 1.50/1.70      inference('sup-', [status(thm)], ['43', '44'])).
% 1.50/1.70  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('47', plain,
% 1.50/1.70      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C @ sk_A))
% 1.50/1.70         != (k2_wellord1 @ sk_C @ sk_A))),
% 1.50/1.70      inference('demod', [status(thm)], ['45', '46'])).
% 1.50/1.70  thf('48', plain,
% 1.50/1.70      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 1.50/1.70        | ~ (v1_relat_1 @ sk_C))),
% 1.50/1.70      inference('sup-', [status(thm)], ['19', '47'])).
% 1.50/1.70  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.50/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.70  thf('50', plain,
% 1.50/1.70      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 1.50/1.70      inference('demod', [status(thm)], ['48', '49'])).
% 1.50/1.70  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 1.50/1.70  
% 1.50/1.70  % SZS output end Refutation
% 1.50/1.70  
% 1.50/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
