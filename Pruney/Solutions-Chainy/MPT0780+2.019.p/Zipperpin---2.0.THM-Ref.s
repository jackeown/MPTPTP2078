%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yLNrXXaYRJ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   77 (  94 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   18
%              Number of atoms          :  591 ( 779 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i] :
      ( ( ( k3_relat_1 @ X33 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ( ( k7_relat_1 @ X36 @ X37 )
        = X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X44 @ X46 ) @ X45 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X44 @ X45 ) @ X46 ) )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X42 @ X43 ) ) @ X43 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X33: $i] :
      ( ( ( k3_relat_1 @ X33 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('34',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( ( k8_relat_1 @ X35 @ X34 )
        = X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X40: $i,X41: $i] :
      ( ( ( k2_wellord1 @ X41 @ X40 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X40 @ X41 ) @ X40 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','47'])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yLNrXXaYRJ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 487 iterations in 0.516s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.97  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.76/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.97  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.97  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.97  thf(t29_wellord1, conjecture,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ C ) =>
% 0.76/0.97       ( ( r1_tarski @ A @ B ) =>
% 0.76/0.97         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.76/0.97           ( k2_wellord1 @ C @ A ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.97        ( ( v1_relat_1 @ C ) =>
% 0.76/0.97          ( ( r1_tarski @ A @ B ) =>
% 0.76/0.97            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 0.76/0.97              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 0.76/0.97  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(t20_wellord1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( r1_tarski @
% 0.76/0.97           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 0.76/0.97         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      (![X42 : $i, X43 : $i]:
% 0.76/0.97         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X42 @ X43)) @ X43)
% 0.76/0.97          | ~ (v1_relat_1 @ X42))),
% 0.76/0.97      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.76/0.97  thf(d6_relat_1, axiom,
% 0.76/0.97    (![A:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) =>
% 0.76/0.97       ( ( k3_relat_1 @ A ) =
% 0.76/0.97         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X33 : $i]:
% 0.76/0.97         (((k3_relat_1 @ X33)
% 0.76/0.97            = (k2_xboole_0 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33)))
% 0.76/0.97          | ~ (v1_relat_1 @ X33))),
% 0.76/0.97      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/0.97  thf(t7_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.76/0.97      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.76/0.97  thf(t1_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.76/0.97       ( r1_tarski @ A @ C ) ))).
% 0.76/0.97  thf('4', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X6 @ X7)
% 0.76/0.97          | ~ (r1_tarski @ X7 @ X8)
% 0.76/0.97          | (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['2', '5'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X1)
% 0.76/0.97          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '6'])).
% 0.76/0.97  thf(dt_k2_wellord1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X38 : $i, X39 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k2_wellord1 @ X38 @ X39)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/0.97  thf('9', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X1))),
% 0.76/0.97      inference('clc', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X6 @ X7)
% 0.76/0.97          | ~ (r1_tarski @ X7 @ X8)
% 0.76/0.97          | (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X1)
% 0.76/0.97          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.76/0.97          | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['9', '10'])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['0', '11'])).
% 0.76/0.97  thf(t97_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.76/0.97         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X36 : $i, X37 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 0.76/0.97          | ((k7_relat_1 @ X36 @ X37) = (X36))
% 0.76/0.97          | ~ (v1_relat_1 @ X36))),
% 0.76/0.97      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.76/0.97  thf('14', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/0.97              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X38 : $i, X39 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k2_wellord1 @ X38 @ X39)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/0.97  thf('16', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/0.97            = (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['14', '15'])).
% 0.76/0.97  thf(t27_wellord1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ C ) =>
% 0.76/0.97       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.76/0.97         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.76/0.97         (((k2_wellord1 @ (k2_wellord1 @ X44 @ X46) @ X45)
% 0.76/0.97            = (k2_wellord1 @ (k2_wellord1 @ X44 @ X45) @ X46))
% 0.76/0.97          | ~ (v1_relat_1 @ X44))),
% 0.76/0.97      inference('cnf', [status(esa)], [t27_wellord1])).
% 0.76/0.97  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('19', plain,
% 0.76/0.97      (![X42 : $i, X43 : $i]:
% 0.76/0.97         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X42 @ X43)) @ X43)
% 0.76/0.97          | ~ (v1_relat_1 @ X42))),
% 0.76/0.97      inference('cnf', [status(esa)], [t20_wellord1])).
% 0.76/0.97  thf('20', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X6 @ X7)
% 0.76/0.97          | ~ (r1_tarski @ X7 @ X8)
% 0.76/0.97          | (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X1)
% 0.76/0.97          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 0.76/0.97          | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['18', '21'])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      (![X33 : $i]:
% 0.76/0.97         (((k3_relat_1 @ X33)
% 0.76/0.97            = (k2_xboole_0 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33)))
% 0.76/0.97          | ~ (v1_relat_1 @ X33))),
% 0.76/0.97      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.76/0.97  thf(d10_xboole_0, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.97      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.97  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.97      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.97  thf(t10_xboole_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.76/0.97         (~ (r1_tarski @ X6 @ X7)
% 0.76/0.97          | ~ (r1_tarski @ X7 @ X8)
% 0.76/0.97          | (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/0.97      inference('sup-', [status(thm)], ['23', '29'])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['22', '30'])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      (![X38 : $i, X39 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k2_wellord1 @ X38 @ X39)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf(t125_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.76/0.97         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      (![X34 : $i, X35 : $i]:
% 0.76/0.97         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 0.76/0.97          | ((k8_relat_1 @ X35 @ X34) = (X34))
% 0.76/0.97          | ~ (v1_relat_1 @ X34))),
% 0.76/0.97      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97              = (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X38 : $i, X39 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k2_wellord1 @ X38 @ X39)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97            = (k2_wellord1 @ X0 @ sk_A))
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('clc', [status(thm)], ['35', '36'])).
% 0.76/0.97  thf(t17_wellord1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ B ) =>
% 0.76/0.97       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 0.76/0.97  thf('38', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i]:
% 0.76/0.97         (((k2_wellord1 @ X41 @ X40)
% 0.76/0.97            = (k7_relat_1 @ (k8_relat_1 @ X40 @ X41) @ X40))
% 0.76/0.97          | ~ (v1_relat_1 @ X41))),
% 0.76/0.97      inference('cnf', [status(esa)], [t17_wellord1])).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/0.97            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['37', '38'])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      (![X38 : $i, X39 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X38) | (v1_relat_1 @ (k2_wellord1 @ X38 @ X39)))),
% 0.76/0.97      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 0.76/0.97  thf('41', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 0.76/0.97              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.76/0.97      inference('clc', [status(thm)], ['39', '40'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.76/0.97            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 0.76/0.97          | ~ (v1_relat_1 @ X0)
% 0.76/0.97          | ~ (v1_relat_1 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['17', '41'])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         (~ (v1_relat_1 @ X0)
% 0.76/0.97          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 0.76/0.97              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['42'])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 0.76/0.97         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.76/0.97          != (k2_wellord1 @ sk_C @ sk_A))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.97  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      (((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 0.76/0.97         != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['45', '46'])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 0.76/0.97        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '47'])).
% 0.76/0.97  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['48', '49'])).
% 0.76/0.97  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
