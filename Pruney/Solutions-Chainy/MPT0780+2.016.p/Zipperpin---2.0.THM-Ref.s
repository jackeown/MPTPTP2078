%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ucuNs56ZMP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:27 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 107 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  618 ( 915 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t19_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( r2_hidden @ X47 @ ( k3_relat_1 @ ( k2_wellord1 @ X48 @ X49 ) ) )
      | ( r2_hidden @ X47 @ X49 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t19_wellord1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('21',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X40 )
      | ( ( k8_relat_1 @ X40 @ X39 )
        = X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X52 ) @ X51 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X50 @ X51 ) @ X52 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('27',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X41 ) @ X42 )
      | ( ( k7_relat_1 @ X41 @ X42 )
        = X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('37',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_wellord1 @ X46 @ X45 )
        = ( k8_relat_1 @ X45 @ ( k7_relat_1 @ X46 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ sk_C_1 @ sk_A ) )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_wellord1 @ sk_C_1 @ sk_A )
     != ( k2_wellord1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ( k2_wellord1 @ sk_C_1 @ sk_A )
 != ( k2_wellord1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(simplify,[status(thm)],['49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ucuNs56ZMP
% 0.14/0.37  % Computer   : n017.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 14:45:01 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.54/2.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.54/2.75  % Solved by: fo/fo7.sh
% 2.54/2.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.54/2.75  % done 1513 iterations in 2.273s
% 2.54/2.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.54/2.75  % SZS output start Refutation
% 2.54/2.75  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 2.54/2.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.54/2.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.54/2.75  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.54/2.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.54/2.75  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.54/2.75  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 2.54/2.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.54/2.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.54/2.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.54/2.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.54/2.75  thf(sk_A_type, type, sk_A: $i).
% 2.54/2.75  thf(sk_B_type, type, sk_B: $i).
% 2.54/2.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.54/2.75  thf(d3_tarski, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( r1_tarski @ A @ B ) <=>
% 2.54/2.75       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.54/2.75  thf('0', plain,
% 2.54/2.75      (![X1 : $i, X3 : $i]:
% 2.54/2.75         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 2.54/2.75      inference('cnf', [status(esa)], [d3_tarski])).
% 2.54/2.75  thf(t19_wellord1, axiom,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ C ) =>
% 2.54/2.75       ( ( r2_hidden @ A @ ( k3_relat_1 @ ( k2_wellord1 @ C @ B ) ) ) =>
% 2.54/2.75         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) ) ))).
% 2.54/2.75  thf('1', plain,
% 2.54/2.75      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.54/2.75         (~ (r2_hidden @ X47 @ (k3_relat_1 @ (k2_wellord1 @ X48 @ X49)))
% 2.54/2.75          | (r2_hidden @ X47 @ X49)
% 2.54/2.75          | ~ (v1_relat_1 @ X48))),
% 2.54/2.75      inference('cnf', [status(esa)], [t19_wellord1])).
% 2.54/2.75  thf('2', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.75         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 2.54/2.75          | ~ (v1_relat_1 @ X1)
% 2.54/2.75          | (r2_hidden @ 
% 2.54/2.75             (sk_C @ X2 @ (k3_relat_1 @ (k2_wellord1 @ X1 @ X0))) @ X0))),
% 2.54/2.75      inference('sup-', [status(thm)], ['0', '1'])).
% 2.54/2.75  thf(t29_wellord1, conjecture,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ C ) =>
% 2.54/2.75       ( ( r1_tarski @ A @ B ) =>
% 2.54/2.75         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 2.54/2.75           ( k2_wellord1 @ C @ A ) ) ) ))).
% 2.54/2.75  thf(zf_stmt_0, negated_conjecture,
% 2.54/2.75    (~( ![A:$i,B:$i,C:$i]:
% 2.54/2.75        ( ( v1_relat_1 @ C ) =>
% 2.54/2.75          ( ( r1_tarski @ A @ B ) =>
% 2.54/2.75            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 2.54/2.75              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 2.54/2.75    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 2.54/2.75  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.54/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.75  thf('4', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.75         (~ (r2_hidden @ X0 @ X1)
% 2.54/2.75          | (r2_hidden @ X0 @ X2)
% 2.54/2.75          | ~ (r1_tarski @ X1 @ X2))),
% 2.54/2.75      inference('cnf', [status(esa)], [d3_tarski])).
% 2.54/2.75  thf('5', plain,
% 2.54/2.75      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 2.54/2.75      inference('sup-', [status(thm)], ['3', '4'])).
% 2.54/2.75  thf('6', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ X1)
% 2.54/2.75          | (r2_hidden @ 
% 2.54/2.75             (sk_C @ X1 @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A))) @ sk_B))),
% 2.54/2.75      inference('sup-', [status(thm)], ['2', '5'])).
% 2.54/2.75  thf('7', plain,
% 2.54/2.75      (![X1 : $i, X3 : $i]:
% 2.54/2.75         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 2.54/2.75      inference('cnf', [status(esa)], [d3_tarski])).
% 2.54/2.75  thf('8', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.54/2.75          | ~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 2.54/2.75      inference('sup-', [status(thm)], ['6', '7'])).
% 2.54/2.75  thf('9', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 2.54/2.75      inference('simplify', [status(thm)], ['8'])).
% 2.54/2.75  thf(d6_relat_1, axiom,
% 2.54/2.75    (![A:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ A ) =>
% 2.54/2.75       ( ( k3_relat_1 @ A ) =
% 2.54/2.75         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.54/2.75  thf('10', plain,
% 2.54/2.75      (![X38 : $i]:
% 2.54/2.75         (((k3_relat_1 @ X38)
% 2.54/2.75            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 2.54/2.75          | ~ (v1_relat_1 @ X38))),
% 2.54/2.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.54/2.75  thf(d10_xboole_0, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.54/2.75  thf('11', plain,
% 2.54/2.75      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.54/2.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.54/2.75  thf('12', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.54/2.75      inference('simplify', [status(thm)], ['11'])).
% 2.54/2.75  thf(t10_xboole_1, axiom,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 2.54/2.75  thf('13', plain,
% 2.54/2.75      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.54/2.75         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 2.54/2.75      inference('cnf', [status(esa)], [t10_xboole_1])).
% 2.54/2.75  thf('14', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 2.54/2.75      inference('sup-', [status(thm)], ['12', '13'])).
% 2.54/2.75  thf(t1_xboole_1, axiom,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.54/2.75       ( r1_tarski @ A @ C ) ))).
% 2.54/2.75  thf('15', plain,
% 2.54/2.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.54/2.75         (~ (r1_tarski @ X13 @ X14)
% 2.54/2.75          | ~ (r1_tarski @ X14 @ X15)
% 2.54/2.75          | (r1_tarski @ X13 @ X15))),
% 2.54/2.75      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.54/2.75  thf('16', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.54/2.75         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.54/2.75      inference('sup-', [status(thm)], ['14', '15'])).
% 2.54/2.75  thf('17', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i]:
% 2.54/2.75         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 2.54/2.75          | ~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.54/2.75      inference('sup-', [status(thm)], ['10', '16'])).
% 2.54/2.75  thf('18', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.54/2.75          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 2.54/2.75      inference('sup-', [status(thm)], ['9', '17'])).
% 2.54/2.75  thf(dt_k2_wellord1, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 2.54/2.75  thf('19', plain,
% 2.54/2.75      (![X43 : $i, X44 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k2_wellord1 @ X43 @ X44)))),
% 2.54/2.75      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.54/2.75  thf('20', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.54/2.75          | ~ (v1_relat_1 @ X0))),
% 2.54/2.75      inference('clc', [status(thm)], ['18', '19'])).
% 2.54/2.75  thf(t125_relat_1, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ B ) =>
% 2.54/2.75       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.54/2.75         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 2.54/2.75  thf('21', plain,
% 2.54/2.75      (![X39 : $i, X40 : $i]:
% 2.54/2.75         (~ (r1_tarski @ (k2_relat_1 @ X39) @ X40)
% 2.54/2.75          | ((k8_relat_1 @ X40 @ X39) = (X39))
% 2.54/2.75          | ~ (v1_relat_1 @ X39))),
% 2.54/2.75      inference('cnf', [status(esa)], [t125_relat_1])).
% 2.54/2.75  thf('22', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75              = (k2_wellord1 @ X0 @ sk_A)))),
% 2.54/2.75      inference('sup-', [status(thm)], ['20', '21'])).
% 2.54/2.75  thf('23', plain,
% 2.54/2.75      (![X43 : $i, X44 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k2_wellord1 @ X43 @ X44)))),
% 2.54/2.75      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.54/2.75  thf('24', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75            = (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75          | ~ (v1_relat_1 @ X0))),
% 2.54/2.75      inference('clc', [status(thm)], ['22', '23'])).
% 2.54/2.75  thf(t27_wellord1, axiom,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ C ) =>
% 2.54/2.75       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 2.54/2.75         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 2.54/2.75  thf('25', plain,
% 2.54/2.75      (![X50 : $i, X51 : $i, X52 : $i]:
% 2.54/2.75         (((k2_wellord1 @ (k2_wellord1 @ X50 @ X52) @ X51)
% 2.54/2.75            = (k2_wellord1 @ (k2_wellord1 @ X50 @ X51) @ X52))
% 2.54/2.75          | ~ (v1_relat_1 @ X50))),
% 2.54/2.75      inference('cnf', [status(esa)], [t27_wellord1])).
% 2.54/2.75  thf('26', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B))),
% 2.54/2.75      inference('simplify', [status(thm)], ['8'])).
% 2.54/2.75  thf('27', plain,
% 2.54/2.75      (![X38 : $i]:
% 2.54/2.75         (((k3_relat_1 @ X38)
% 2.54/2.75            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 2.54/2.75          | ~ (v1_relat_1 @ X38))),
% 2.54/2.75      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.54/2.75  thf(t11_xboole_1, axiom,
% 2.54/2.75    (![A:$i,B:$i,C:$i]:
% 2.54/2.75     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.54/2.75  thf('28', plain,
% 2.54/2.75      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.54/2.75         ((r1_tarski @ X10 @ X11)
% 2.54/2.75          | ~ (r1_tarski @ (k2_xboole_0 @ X10 @ X12) @ X11))),
% 2.54/2.75      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.54/2.75  thf('29', plain,
% 2.54/2.75      (![X0 : $i, X1 : $i]:
% 2.54/2.75         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 2.54/2.75          | ~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 2.54/2.75      inference('sup-', [status(thm)], ['27', '28'])).
% 2.54/2.75  thf('30', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | (r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.54/2.75          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 2.54/2.75      inference('sup-', [status(thm)], ['26', '29'])).
% 2.54/2.75  thf('31', plain,
% 2.54/2.75      (![X43 : $i, X44 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k2_wellord1 @ X43 @ X44)))),
% 2.54/2.75      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.54/2.75  thf('32', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         ((r1_tarski @ (k1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.54/2.75          | ~ (v1_relat_1 @ X0))),
% 2.54/2.75      inference('clc', [status(thm)], ['30', '31'])).
% 2.54/2.75  thf(t97_relat_1, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ B ) =>
% 2.54/2.75       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.54/2.75         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 2.54/2.75  thf('33', plain,
% 2.54/2.75      (![X41 : $i, X42 : $i]:
% 2.54/2.75         (~ (r1_tarski @ (k1_relat_1 @ X41) @ X42)
% 2.54/2.75          | ((k7_relat_1 @ X41 @ X42) = (X41))
% 2.54/2.75          | ~ (v1_relat_1 @ X41))),
% 2.54/2.75      inference('cnf', [status(esa)], [t97_relat_1])).
% 2.54/2.75  thf('34', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.54/2.75              = (k2_wellord1 @ X0 @ sk_A)))),
% 2.54/2.75      inference('sup-', [status(thm)], ['32', '33'])).
% 2.54/2.75  thf('35', plain,
% 2.54/2.75      (![X43 : $i, X44 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k2_wellord1 @ X43 @ X44)))),
% 2.54/2.75      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.54/2.75  thf('36', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.54/2.75            = (k2_wellord1 @ X0 @ sk_A))
% 2.54/2.75          | ~ (v1_relat_1 @ X0))),
% 2.54/2.75      inference('clc', [status(thm)], ['34', '35'])).
% 2.54/2.75  thf(t18_wellord1, axiom,
% 2.54/2.75    (![A:$i,B:$i]:
% 2.54/2.75     ( ( v1_relat_1 @ B ) =>
% 2.54/2.75       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 2.54/2.75  thf('37', plain,
% 2.54/2.75      (![X45 : $i, X46 : $i]:
% 2.54/2.75         (((k2_wellord1 @ X46 @ X45)
% 2.54/2.75            = (k8_relat_1 @ X45 @ (k7_relat_1 @ X46 @ X45)))
% 2.54/2.75          | ~ (v1_relat_1 @ X46))),
% 2.54/2.75      inference('cnf', [status(esa)], [t18_wellord1])).
% 2.54/2.75  thf('38', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.54/2.75            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 2.54/2.75          | ~ (v1_relat_1 @ X0)
% 2.54/2.75          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 2.54/2.75      inference('sup+', [status(thm)], ['36', '37'])).
% 2.54/2.75  thf('39', plain,
% 2.54/2.75      (![X43 : $i, X44 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X43) | (v1_relat_1 @ (k2_wellord1 @ X43 @ X44)))),
% 2.54/2.75      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.54/2.75  thf('40', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.54/2.75              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 2.54/2.75      inference('clc', [status(thm)], ['38', '39'])).
% 2.54/2.75  thf('41', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 2.54/2.75            = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A)))
% 2.54/2.75          | ~ (v1_relat_1 @ X0)
% 2.54/2.75          | ~ (v1_relat_1 @ X0))),
% 2.54/2.75      inference('sup+', [status(thm)], ['25', '40'])).
% 2.54/2.75  thf('42', plain,
% 2.54/2.75      (![X0 : $i]:
% 2.54/2.75         (~ (v1_relat_1 @ X0)
% 2.54/2.75          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 2.54/2.75              = (k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))))),
% 2.54/2.75      inference('simplify', [status(thm)], ['41'])).
% 2.54/2.75  thf('43', plain,
% 2.54/2.75      (((k2_wellord1 @ (k2_wellord1 @ sk_C_1 @ sk_B) @ sk_A)
% 2.54/2.75         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 2.54/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.75  thf('44', plain,
% 2.54/2.75      ((((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 2.54/2.75          != (k2_wellord1 @ sk_C_1 @ sk_A))
% 2.54/2.75        | ~ (v1_relat_1 @ sk_C_1))),
% 2.54/2.75      inference('sup-', [status(thm)], ['42', '43'])).
% 2.54/2.75  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 2.54/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.75  thf('46', plain,
% 2.54/2.75      (((k8_relat_1 @ sk_B @ (k2_wellord1 @ sk_C_1 @ sk_A))
% 2.54/2.75         != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 2.54/2.75      inference('demod', [status(thm)], ['44', '45'])).
% 2.54/2.75  thf('47', plain,
% 2.54/2.75      ((((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))
% 2.54/2.75        | ~ (v1_relat_1 @ sk_C_1))),
% 2.54/2.75      inference('sup-', [status(thm)], ['24', '46'])).
% 2.54/2.75  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 2.54/2.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.54/2.75  thf('49', plain,
% 2.54/2.75      (((k2_wellord1 @ sk_C_1 @ sk_A) != (k2_wellord1 @ sk_C_1 @ sk_A))),
% 2.54/2.75      inference('demod', [status(thm)], ['47', '48'])).
% 2.54/2.75  thf('50', plain, ($false), inference('simplify', [status(thm)], ['49'])).
% 2.54/2.75  
% 2.54/2.75  % SZS output end Refutation
% 2.54/2.75  
% 2.54/2.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
