%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MBhvqpwiRr

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 224 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  540 (1781 expanded)
%              Number of equality atoms :   49 ( 159 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t43_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
        = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_funct_1])).

thf('0',plain,(
    ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X10 ) @ ( k4_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X16 ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('23',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ X17 @ ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('28',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) @ X9 )
        = ( k7_relat_1 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
      = ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','34'])).

thf('36',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','34'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_relat_1 @ X19 @ X18 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X18 ) @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_relat_1 @ ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','22','34'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
        = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','44','45'])).

thf('47',plain,(
    ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k6_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MBhvqpwiRr
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 13:56:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 62 iterations in 0.078s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.22/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(t43_funct_1, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.54       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.22/0.54          ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t43_funct_1])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.22/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t94_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.54  thf(t72_relat_1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X14 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X14)) = (k6_relat_1 @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X14 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X14)) = (k6_relat_1 @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.22/0.54  thf(t54_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( v1_relat_1 @ B ) =>
% 0.22/0.54           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.22/0.54             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X10)
% 0.22/0.54          | ((k4_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 0.22/0.54              = (k5_relat_1 @ (k4_relat_1 @ X10) @ (k4_relat_1 @ X11)))
% 0.22/0.54          | ~ (v1_relat_1 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.22/0.54          | ~ (v1_relat_1 @ X1)
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.54  thf('6', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.22/0.54            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.22/0.54          | ~ (v1_relat_1 @ X1))),
% 0.22/0.54      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.22/0.54            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['2', '7'])).
% 0.22/0.54  thf('9', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1)))
% 0.22/0.54           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.54            = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['1', '10'])).
% 0.22/0.54  thf('12', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.54           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ sk_B) @ sk_A))
% 0.22/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '13'])).
% 0.22/0.54  thf(t17_xboole_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.22/0.54  thf(t71_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.54  thf('16', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf(t77_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.54         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.22/0.54          | ((k5_relat_1 @ (k6_relat_1 @ X16) @ X15) = (X15))
% 0.22/0.54          | ~ (v1_relat_1 @ X15))),
% 0.22/0.54      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.54          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.22/0.54              = (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.54  thf('19', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.54          | ((k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0))
% 0.22/0.54              = (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k5_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.22/0.54           (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.54           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf(t80_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X17 : $i]:
% 0.22/0.54         (((k5_relat_1 @ X17 @ (k6_relat_1 @ (k2_relat_1 @ X17))) = (X17))
% 0.22/0.54          | ~ (v1_relat_1 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.22/0.54            = (k6_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.54  thf('26', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf('27', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('28', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.54  thf('29', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.22/0.54  thf(t100_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ C ) =>
% 0.22/0.54       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.54         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.54         (((k7_relat_1 @ (k7_relat_1 @ X7 @ X8) @ X9)
% 0.22/0.54            = (k7_relat_1 @ X7 @ (k3_xboole_0 @ X8 @ X9)))
% 0.22/0.54          | ~ (v1_relat_1 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.54            = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['30', '31'])).
% 0.22/0.54  thf('33', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k7_relat_1 @ (k6_relat_1 @ X0) @ X1)
% 0.22/0.54           = (k7_relat_1 @ (k6_relat_1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '22', '34'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (((k6_relat_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.22/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['14', '35'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '22', '34'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X18 : $i, X19 : $i]:
% 0.22/0.54         (((k7_relat_1 @ X19 @ X18) = (k5_relat_1 @ (k6_relat_1 @ X18) @ X19))
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.54           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k4_relat_1 @ (k7_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.22/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '22', '34'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.54           = (k5_relat_1 @ (k6_relat_1 @ X1) @ (k6_relat_1 @ X0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.22/0.54            = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))
% 0.22/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['38', '41'])).
% 0.22/0.54  thf('43', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k6_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.22/0.54           = (k7_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.22/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X14 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X14)) = (k6_relat_1 @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.54           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.54      inference('demod', [status(thm)], ['37', '44', '45'])).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (((k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.22/0.54         != (k6_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '46'])).
% 0.22/0.54  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
