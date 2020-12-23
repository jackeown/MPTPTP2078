%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IjQx1BmYN1

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:26 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 206 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   19
%              Number of atoms          :  506 (1313 expanded)
%              Number of equality atoms :   41 ( 105 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('0',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('2',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_xboole_0 @ X53 @ ( k1_tarski @ X52 ) )
        = ( k1_tarski @ X52 ) )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup+',[status(thm)],['3','7'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X43: $i,X45: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X43 ) @ X45 )
        = ( k1_tarski @ X43 ) )
      | ( r2_hidden @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X42: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X42 @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf('19',plain,(
    ! [X42: $i] :
      ( ( k3_enumset1 @ X42 @ X42 @ X42 @ X42 @ X42 )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r2_hidden @ X50 @ X51 )
      | ( ( k3_xboole_0 @ X51 @ ( k1_tarski @ X50 ) )
       != ( k1_tarski @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X15 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t89_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t89_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','39'])).

thf(t54_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('41',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
      | ~ ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t54_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['17','44'])).

thf('46',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_xboole_0 @ X53 @ ( k1_tarski @ X52 ) )
        = ( k1_tarski @ X52 ) )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t52_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','53'])).

thf('55',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IjQx1BmYN1
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 1855 iterations in 0.674s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.90/1.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.90/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.90/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(t55_zfmisc_1, conjecture,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i,B:$i,C:$i]:
% 0.90/1.13        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.90/1.13             ( r2_hidden @ A @ C ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.90/1.13  thf('0', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('1', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t52_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( r2_hidden @ A @ B ) =>
% 0.90/1.13       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.90/1.13  thf('2', plain,
% 0.90/1.13      (![X52 : $i, X53 : $i]:
% 0.90/1.13         (((k3_xboole_0 @ X53 @ (k1_tarski @ X52)) = (k1_tarski @ X52))
% 0.90/1.13          | ~ (r2_hidden @ X52 @ X53))),
% 0.90/1.13      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['1', '2'])).
% 0.90/1.13  thf(d10_xboole_0, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.13      inference('simplify', [status(thm)], ['4'])).
% 0.90/1.13  thf(t18_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.90/1.13         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.90/1.13      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.90/1.13      inference('sup+', [status(thm)], ['3', '7'])).
% 0.90/1.13  thf(l33_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.90/1.13       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X43 : $i, X45 : $i]:
% 0.90/1.13         (((k4_xboole_0 @ (k1_tarski @ X43) @ X45) = (k1_tarski @ X43))
% 0.90/1.13          | (r2_hidden @ X43 @ X45))),
% 0.90/1.13      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.90/1.13  thf(t48_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      (![X10 : $i, X11 : $i]:
% 0.90/1.13         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.90/1.13           = (k3_xboole_0 @ X10 @ X11))),
% 0.90/1.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.90/1.13  thf('11', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.90/1.13            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | (r2_hidden @ X0 @ X1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['9', '10'])).
% 0.90/1.13  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.90/1.13      inference('simplify', [status(thm)], ['4'])).
% 0.90/1.13  thf(t37_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      (![X7 : $i, X9 : $i]:
% 0.90/1.13         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.90/1.13  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.90/1.13          | (r2_hidden @ X0 @ X1))),
% 0.90/1.13      inference('demod', [status(thm)], ['11', '14'])).
% 0.90/1.13  thf(t19_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.90/1.13       ( k1_tarski @ A ) ))).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X48 : $i, X49 : $i]:
% 0.90/1.13         ((k3_xboole_0 @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))
% 0.90/1.13           = (k1_tarski @ X48))),
% 0.90/1.13      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.90/1.13  thf('17', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.90/1.13          | (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['15', '16'])).
% 0.90/1.13  thf(t87_enumset1, axiom,
% 0.90/1.13    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X42 : $i]:
% 0.90/1.13         ((k3_enumset1 @ X42 @ X42 @ X42 @ X42 @ X42) = (k1_tarski @ X42))),
% 0.90/1.13      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      (![X42 : $i]:
% 0.90/1.13         ((k3_enumset1 @ X42 @ X42 @ X42 @ X42 @ X42) = (k1_tarski @ X42))),
% 0.90/1.13      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.90/1.13  thf('20', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf(t2_boole, axiom,
% 0.90/1.13    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.13      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.13      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      (![X0 : $i, X2 : $i]:
% 0.90/1.13         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.90/1.13      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['23', '24'])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['20', '25'])).
% 0.90/1.13  thf(t51_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.90/1.13       ( r2_hidden @ B @ A ) ))).
% 0.90/1.13  thf('27', plain,
% 0.90/1.13      (![X50 : $i, X51 : $i]:
% 0.90/1.13         ((r2_hidden @ X50 @ X51)
% 0.90/1.13          | ((k3_xboole_0 @ X51 @ (k1_tarski @ X50)) != (k1_tarski @ X50)))),
% 0.90/1.13      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['26', '27'])).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (((k1_xboole_0) != (k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0))
% 0.90/1.13          | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['19', '28'])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.90/1.13      inference('cnf', [status(esa)], [t2_boole])).
% 0.90/1.13  thf(t75_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.13          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i]:
% 0.90/1.13         ((r1_xboole_0 @ X15 @ X16)
% 0.90/1.13          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X15 @ X16) @ X16))),
% 0.90/1.13      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.90/1.13          | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['30', '31'])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['20', '25'])).
% 0.90/1.13  thf(t89_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ))).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      (![X17 : $i, X18 : $i]:
% 0.90/1.13         (r1_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))),
% 0.90/1.13      inference('cnf', [status(esa)], [t89_xboole_1])).
% 0.90/1.13  thf('35', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.90/1.13      inference('sup+', [status(thm)], ['33', '34'])).
% 0.90/1.13  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.90/1.13      inference('sup+', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      (![X7 : $i, X9 : $i]:
% 0.90/1.13         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.90/1.13      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['36', '37'])).
% 0.90/1.13  thf('39', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.90/1.13      inference('demod', [status(thm)], ['35', '38'])).
% 0.90/1.13  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.90/1.13      inference('demod', [status(thm)], ['32', '39'])).
% 0.90/1.13  thf(t54_zfmisc_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.90/1.13  thf('41', plain,
% 0.90/1.13      (![X54 : $i, X55 : $i]:
% 0.90/1.13         (~ (r1_xboole_0 @ (k1_tarski @ X54) @ X55) | ~ (r2_hidden @ X54 @ X55))),
% 0.90/1.13      inference('cnf', [status(esa)], [t54_zfmisc_1])).
% 0.90/1.13  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.13      inference('sup-', [status(thm)], ['40', '41'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      (![X0 : $i]: ((k1_xboole_0) != (k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0))),
% 0.90/1.13      inference('clc', [status(thm)], ['29', '42'])).
% 0.90/1.13  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['18', '43'])).
% 0.90/1.13  thf('45', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.90/1.13      inference('clc', [status(thm)], ['17', '44'])).
% 0.90/1.13  thf('46', plain,
% 0.90/1.13      (![X52 : $i, X53 : $i]:
% 0.90/1.13         (((k3_xboole_0 @ X53 @ (k1_tarski @ X52)) = (k1_tarski @ X52))
% 0.90/1.13          | ~ (r2_hidden @ X52 @ X53))),
% 0.90/1.13      inference('cnf', [status(esa)], [t52_zfmisc_1])).
% 0.90/1.13  thf('47', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.90/1.13           = (k1_tarski @ X1))),
% 0.90/1.13      inference('sup-', [status(thm)], ['45', '46'])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))),
% 0.90/1.13      inference('sup+', [status(thm)], ['47', '48'])).
% 0.90/1.13  thf(t67_xboole_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.90/1.13         ( r1_xboole_0 @ B @ C ) ) =>
% 0.90/1.13       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.13         (((X12) = (k1_xboole_0))
% 0.90/1.13          | ~ (r1_tarski @ X12 @ X13)
% 0.90/1.13          | ~ (r1_tarski @ X12 @ X14)
% 0.90/1.13          | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.90/1.13      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.90/1.13  thf('51', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.90/1.13          | ~ (r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.90/1.13          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['49', '50'])).
% 0.90/1.13  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.90/1.13      inference('sup-', [status(thm)], ['18', '43'])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.90/1.13          | ~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.90/1.13      inference('clc', [status(thm)], ['51', '52'])).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (![X0 : $i]: ~ (r1_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['8', '53'])).
% 0.90/1.13  thf('55', plain, ($false), inference('sup-', [status(thm)], ['0', '54'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
