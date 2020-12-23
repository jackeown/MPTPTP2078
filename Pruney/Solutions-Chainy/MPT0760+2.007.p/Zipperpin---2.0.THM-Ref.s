%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8iQDwERTle

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:20 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 105 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  635 ( 940 expanded)
%              Number of equality atoms :   47 (  69 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X48: $i] :
      ( ( X48
        = ( k2_relat_1 @ X45 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X48 @ X45 ) @ ( sk_C @ X48 @ X45 ) ) @ X45 )
      | ( r2_hidden @ ( sk_C @ X48 @ X45 ) @ X48 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ ( sk_D_2 @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('7',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( X56
       != ( k1_wellord1 @ X55 @ X54 ) )
      | ( r2_hidden @ ( k4_tarski @ X57 @ X54 ) @ X55 )
      | ~ ( r2_hidden @ X57 @ X56 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('12',plain,(
    ! [X54: $i,X55: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X55 )
      | ~ ( r2_hidden @ X57 @ ( k1_wellord1 @ X55 @ X54 ) )
      | ( r2_hidden @ ( k4_tarski @ X57 @ X54 ) @ X55 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord1 @ X1 @ X0 ) @ k1_xboole_0 ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X43 @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X46 )
      | ( X46
       != ( k2_relat_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('15',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ X44 @ ( k2_relat_1 @ X45 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X43 @ X44 ) @ X45 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X50: $i] :
      ( ( ( k3_relat_1 @ X50 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k2_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k3_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X41 @ X42 ) )
      = ( k3_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_wellord1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_wellord1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_wellord1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8iQDwERTle
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 341 iterations in 0.274s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.70  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.70  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.70  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.45/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.70  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.70  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.45/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.70  thf('0', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.70  thf(d5_relat_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.70       ( ![C:$i]:
% 0.45/0.70         ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      (![X45 : $i, X48 : $i]:
% 0.45/0.70         (((X48) = (k2_relat_1 @ X45))
% 0.45/0.70          | (r2_hidden @ 
% 0.45/0.70             (k4_tarski @ (sk_D_2 @ X48 @ X45) @ (sk_C @ X48 @ X45)) @ X45)
% 0.45/0.70          | (r2_hidden @ (sk_C @ X48 @ X45) @ X48))),
% 0.45/0.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.70  thf(t7_ordinal1, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (![X51 : $i, X52 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.45/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.45/0.70          | ((X1) = (k2_relat_1 @ X0))
% 0.45/0.70          | ~ (r1_tarski @ X0 @ 
% 0.45/0.70               (k4_tarski @ (sk_D_2 @ X1 @ X0) @ (sk_C @ X1 @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.70  thf('5', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X51 : $i, X52 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X51 @ X52) | ~ (r1_tarski @ X52 @ X51))),
% 0.45/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.45/0.70          | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.70  thf('9', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.70  thf('10', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['4', '9'])).
% 0.45/0.70  thf(d1_wellord1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ A ) =>
% 0.45/0.70       ( ![B:$i,C:$i]:
% 0.45/0.70         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.45/0.70           ( ![D:$i]:
% 0.45/0.70             ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.70               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.45/0.70         (((X56) != (k1_wellord1 @ X55 @ X54))
% 0.45/0.70          | (r2_hidden @ (k4_tarski @ X57 @ X54) @ X55)
% 0.45/0.70          | ~ (r2_hidden @ X57 @ X56)
% 0.45/0.70          | ~ (v1_relat_1 @ X55))),
% 0.45/0.70      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X54 : $i, X55 : $i, X57 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X55)
% 0.45/0.70          | ~ (r2_hidden @ X57 @ (k1_wellord1 @ X55 @ X54))
% 0.45/0.70          | (r2_hidden @ (k4_tarski @ X57 @ X54) @ X55))),
% 0.45/0.70      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_wellord1 @ X1 @ X0) = (k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ 
% 0.45/0.70             (k4_tarski @ (sk_C @ (k1_wellord1 @ X1 @ X0) @ k1_xboole_0) @ X0) @ 
% 0.45/0.70             X1)
% 0.45/0.70          | ~ (v1_relat_1 @ X1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '12'])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.45/0.70         (~ (r2_hidden @ (k4_tarski @ X43 @ X44) @ X45)
% 0.45/0.70          | (r2_hidden @ X44 @ X46)
% 0.45/0.70          | ((X46) != (k2_relat_1 @ X45)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.45/0.70         ((r2_hidden @ X44 @ (k2_relat_1 @ X45))
% 0.45/0.70          | ~ (r2_hidden @ (k4_tarski @ X43 @ X44) @ X45))),
% 0.45/0.70      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ X0)
% 0.45/0.70          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 0.45/0.70          | (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.70  thf(d6_relat_1, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ A ) =>
% 0.45/0.70       ( ( k3_relat_1 @ A ) =
% 0.45/0.70         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X50 : $i]:
% 0.45/0.70         (((k3_relat_1 @ X50)
% 0.45/0.70            = (k2_xboole_0 @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X50)))
% 0.45/0.70          | ~ (v1_relat_1 @ X50))),
% 0.45/0.70      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.70  thf(d4_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.70       ( ![D:$i]:
% 0.45/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.70           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.45/0.70         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.45/0.70          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.45/0.70          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.70  thf(t12_setfam_1, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.45/0.70         (((X11) = (k1_setfam_1 @ (k2_tarski @ X7 @ X8)))
% 0.45/0.70          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.45/0.70          | (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.45/0.70      inference('eq_fact', [status(thm)], ['20'])).
% 0.45/0.70  thf(d3_xboole_0, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.45/0.70       ( ![D:$i]:
% 0.45/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.70          | (r2_hidden @ X0 @ X2)
% 0.45/0.70          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.45/0.70         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.70      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.45/0.70          | (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['21', '23'])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.45/0.70      inference('eq_fact', [status(thm)], ['20'])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.45/0.70         (((X11) = (k3_xboole_0 @ X7 @ X8))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.45/0.70         (((X11) = (k1_setfam_1 @ (k2_tarski @ X7 @ X8)))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X8)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X7)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X11 @ X8 @ X7) @ X11))),
% 0.45/0.70      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1)
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['25', '28'])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1)
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X0)
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.45/0.70      inference('eq_fact', [status(thm)], ['20'])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D_1 @ X0 @ X0 @ X1) @ X1))),
% 0.45/0.70      inference('clc', [status(thm)], ['30', '31'])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X0) = (k1_setfam_1 @ (k2_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)))
% 0.45/0.70          | ((X0) = (k1_setfam_1 @ (k2_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['24', '32'])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((X0) = (k1_setfam_1 @ (k2_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_relat_1 @ X0)
% 0.45/0.70            = (k1_setfam_1 @ 
% 0.45/0.70               (k2_tarski @ (k3_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.70          | ~ (v1_relat_1 @ X0))),
% 0.45/0.70      inference('sup+', [status(thm)], ['17', '34'])).
% 0.45/0.70  thf('36', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X10 @ X9)
% 0.45/0.70          | (r2_hidden @ X10 @ X7)
% 0.45/0.70          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.70      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.45/0.70         ((r2_hidden @ X10 @ X7)
% 0.45/0.70          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['36'])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (![X41 : $i, X42 : $i]:
% 0.45/0.70         ((k1_setfam_1 @ (k2_tarski @ X41 @ X42)) = (k3_xboole_0 @ X41 @ X42))),
% 0.45/0.70      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.45/0.70         ((r2_hidden @ X10 @ X7)
% 0.45/0.70          | ~ (r2_hidden @ X10 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.45/0.70      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.70  thf('40', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['35', '39'])).
% 0.45/0.70  thf('41', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k1_wellord1 @ X0 @ X1) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['16', '40'])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | ((k1_wellord1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.70  thf(t2_wellord1, conjecture,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( v1_relat_1 @ B ) =>
% 0.45/0.70       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.45/0.70         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i,B:$i]:
% 0.45/0.70        ( ( v1_relat_1 @ B ) =>
% 0.45/0.70          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.45/0.70            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.45/0.70  thf('43', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      ((((k1_wellord1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.70      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.70  thf('45', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('46', plain, (((k1_wellord1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.45/0.70  thf('47', plain, (((k1_wellord1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('48', plain, ($false),
% 0.45/0.70      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.54/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
