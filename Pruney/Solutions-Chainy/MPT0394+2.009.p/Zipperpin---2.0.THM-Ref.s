%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0r4uw3Knwz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:45 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 208 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  535 (1533 expanded)
%              Number of equality atoms :   62 ( 177 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X18 @ X19 @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X18 @ X19 @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X37 @ X38 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X37 ) @ ( k1_setfam_1 @ X38 ) ) )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) )
      | ( X35 != X36 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X36: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('33',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','43'])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','44'])).

thf('46',plain,(
    ! [X36: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X36 ) @ ( k1_tarski @ X36 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('47',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','44'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0r4uw3Knwz
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.57/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.57/0.77  % Solved by: fo/fo7.sh
% 0.57/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.77  % done 760 iterations in 0.308s
% 0.57/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.57/0.77  % SZS output start Refutation
% 0.57/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.57/0.77  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.77  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.77  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.77  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.57/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.77  thf(t69_enumset1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.77  thf('0', plain, (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.57/0.77      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.77  thf(t71_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i]:
% 0.57/0.77     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.57/0.77  thf('1', plain,
% 0.57/0.77      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.57/0.77           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.57/0.77      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.57/0.77  thf(t70_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.77  thf('2', plain,
% 0.57/0.77      (![X28 : $i, X29 : $i]:
% 0.57/0.77         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.57/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.77  thf('3', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['1', '2'])).
% 0.57/0.77  thf('4', plain,
% 0.57/0.77      (![X28 : $i, X29 : $i]:
% 0.57/0.77         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.57/0.77      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.77  thf(t46_enumset1, axiom,
% 0.57/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.77     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.57/0.77       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.57/0.77  thf('5', plain,
% 0.57/0.77      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X18 @ X19 @ X20 @ X21)
% 0.57/0.77           = (k2_xboole_0 @ (k1_enumset1 @ X18 @ X19 @ X20) @ (k1_tarski @ X21)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.57/0.77  thf('6', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.77         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.57/0.77           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.77  thf('7', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_tarski @ X1 @ X0)
% 0.57/0.77           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['3', '6'])).
% 0.57/0.77  thf('8', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         ((k2_tarski @ X0 @ X1)
% 0.57/0.77           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['0', '7'])).
% 0.57/0.77  thf(t11_setfam_1, axiom,
% 0.57/0.77    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.77  thf('9', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.57/0.77      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.57/0.77  thf(t10_setfam_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.57/0.77          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.57/0.77            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.57/0.77  thf('10', plain,
% 0.57/0.77      (![X37 : $i, X38 : $i]:
% 0.57/0.77         (((X37) = (k1_xboole_0))
% 0.57/0.77          | ((k1_setfam_1 @ (k2_xboole_0 @ X37 @ X38))
% 0.57/0.77              = (k3_xboole_0 @ (k1_setfam_1 @ X37) @ (k1_setfam_1 @ X38)))
% 0.57/0.77          | ((X38) = (k1_xboole_0)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.57/0.77  thf('11', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.57/0.77            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.57/0.77          | ((X1) = (k1_xboole_0))
% 0.57/0.77          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.77  thf('12', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.57/0.77            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.57/0.77          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.57/0.77          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup+', [status(thm)], ['8', '11'])).
% 0.57/0.77  thf('13', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 0.57/0.77      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.57/0.77  thf('14', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.57/0.77          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.57/0.77          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.77      inference('demod', [status(thm)], ['12', '13'])).
% 0.57/0.77  thf(t12_setfam_1, conjecture,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.77    (~( ![A:$i,B:$i]:
% 0.57/0.77        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.57/0.77    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.57/0.77  thf('15', plain,
% 0.57/0.77      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.57/0.77         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.57/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.77  thf('16', plain,
% 0.57/0.77      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.57/0.77        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.57/0.77        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.77  thf('17', plain,
% 0.57/0.77      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.57/0.77        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.57/0.77      inference('simplify', [status(thm)], ['16'])).
% 0.57/0.77  thf(t16_zfmisc_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.57/0.77          ( ( A ) = ( B ) ) ) ))).
% 0.57/0.77  thf('18', plain,
% 0.57/0.77      (![X35 : $i, X36 : $i]:
% 0.57/0.77         (~ (r1_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X36))
% 0.57/0.77          | ((X35) != (X36)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.57/0.77  thf('19', plain,
% 0.57/0.77      (![X36 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))),
% 0.57/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.77  thf('20', plain,
% 0.57/0.77      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.57/0.77        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.57/0.77      inference('sup-', [status(thm)], ['17', '19'])).
% 0.57/0.77  thf(t3_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.57/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.57/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.57/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.57/0.77  thf('21', plain,
% 0.57/0.77      (![X2 : $i, X3 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.77  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.77  thf('22', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.77  thf(t2_boole, axiom,
% 0.57/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.57/0.77  thf('23', plain,
% 0.57/0.77      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.57/0.77  thf('24', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.57/0.77  thf(t4_xboole_0, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.57/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.57/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.57/0.77            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.57/0.77  thf('25', plain,
% 0.57/0.77      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.57/0.77          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.57/0.77  thf('26', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.57/0.77  thf(t48_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('27', plain,
% 0.57/0.77      (![X13 : $i, X14 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.57/0.77           = (k3_xboole_0 @ X13 @ X14))),
% 0.57/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.77  thf('28', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.57/0.77  thf(t47_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.57/0.77  thf('29', plain,
% 0.57/0.77      (![X11 : $i, X12 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.57/0.77           = (k4_xboole_0 @ X11 @ X12))),
% 0.57/0.77      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.57/0.77  thf('30', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['28', '29'])).
% 0.57/0.77  thf('31', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.57/0.77           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['27', '30'])).
% 0.57/0.77  thf('32', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.57/0.77  thf('33', plain,
% 0.57/0.77      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['31', '32'])).
% 0.57/0.77  thf(t83_xboole_1, axiom,
% 0.57/0.77    (![A:$i,B:$i]:
% 0.57/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.77  thf('34', plain,
% 0.57/0.77      (![X15 : $i, X17 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.57/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.57/0.77  thf('35', plain,
% 0.57/0.77      ((((k1_xboole_0) != (k1_xboole_0))
% 0.57/0.77        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['33', '34'])).
% 0.57/0.77  thf('36', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.57/0.77      inference('simplify', [status(thm)], ['35'])).
% 0.57/0.77  thf('37', plain,
% 0.57/0.77      (![X2 : $i, X3 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.57/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.57/0.77  thf('38', plain,
% 0.57/0.77      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.57/0.77         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.57/0.77          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.57/0.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.57/0.77  thf('39', plain,
% 0.57/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.77         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.57/0.77          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.57/0.77      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.77  thf('40', plain,
% 0.57/0.77      (![X0 : $i]:
% 0.57/0.77         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.57/0.77      inference('sup-', [status(thm)], ['36', '39'])).
% 0.57/0.77  thf('41', plain,
% 0.57/0.77      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.77      inference('sup+', [status(thm)], ['22', '23'])).
% 0.57/0.77  thf('42', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.77      inference('demod', [status(thm)], ['40', '41'])).
% 0.57/0.77  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.57/0.77      inference('demod', [status(thm)], ['26', '42'])).
% 0.57/0.77  thf('44', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.57/0.77      inference('sup-', [status(thm)], ['21', '43'])).
% 0.57/0.77  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['20', '44'])).
% 0.57/0.77  thf('46', plain,
% 0.57/0.77      (![X36 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X36) @ (k1_tarski @ X36))),
% 0.57/0.77      inference('simplify', [status(thm)], ['18'])).
% 0.57/0.77  thf('47', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.57/0.77      inference('sup-', [status(thm)], ['45', '46'])).
% 0.57/0.77  thf('48', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.57/0.77      inference('demod', [status(thm)], ['20', '44'])).
% 0.57/0.77  thf('49', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.57/0.77      inference('demod', [status(thm)], ['40', '41'])).
% 0.57/0.77  thf('50', plain, ($false),
% 0.57/0.77      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.57/0.77  
% 0.57/0.77  % SZS output end Refutation
% 0.57/0.77  
% 0.57/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
