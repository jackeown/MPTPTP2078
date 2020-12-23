%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3M3bNlJ1wo

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 275 expanded)
%              Number of leaves         :   31 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :  559 (1888 expanded)
%              Number of equality atoms :   63 ( 188 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X21 @ X22 @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X42: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X40 ) @ ( k1_setfam_1 @ X41 ) ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X42: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X42 ) )
      = X42 ) ),
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
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X39 ) )
      | ( X38 != X39 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X39: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X39 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( ( k3_xboole_0 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('37',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','47'])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','48'])).

thf('50',plain,(
    ! [X39: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('51',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','48'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3M3bNlJ1wo
% 0.17/0.37  % Computer   : n004.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 13:47:39 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 665 iterations in 0.420s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.86  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.67/0.86  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.67/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(t70_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.67/0.86  thf('0', plain,
% 0.67/0.86      (![X31 : $i, X32 : $i]:
% 0.67/0.86         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.86  thf(t69_enumset1, axiom,
% 0.67/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.67/0.86  thf('1', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.67/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['0', '1'])).
% 0.67/0.86  thf(t46_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.67/0.86       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.67/0.86  thf('3', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.67/0.86           = (k2_xboole_0 @ (k1_enumset1 @ X21 @ X22 @ X23) @ (k1_tarski @ X24)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.67/0.86  thf('4', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.67/0.86           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf(t71_enumset1, axiom,
% 0.67/0.86    (![A:$i,B:$i,C:$i]:
% 0.67/0.86     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.67/0.86  thf('5', plain,
% 0.67/0.86      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 0.67/0.86           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.67/0.86      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.67/0.86  thf('6', plain,
% 0.67/0.86      (![X31 : $i, X32 : $i]:
% 0.67/0.86         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.67/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.67/0.86  thf('7', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['5', '6'])).
% 0.67/0.86  thf('8', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.67/0.86           = (k2_tarski @ X1 @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['4', '7'])).
% 0.67/0.86  thf(t11_setfam_1, axiom,
% 0.67/0.86    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.67/0.86  thf('9', plain, (![X42 : $i]: ((k1_setfam_1 @ (k1_tarski @ X42)) = (X42))),
% 0.67/0.86      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.67/0.86  thf(t10_setfam_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.67/0.86          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.67/0.86            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.67/0.86  thf('10', plain,
% 0.67/0.86      (![X40 : $i, X41 : $i]:
% 0.67/0.86         (((X40) = (k1_xboole_0))
% 0.67/0.86          | ((k1_setfam_1 @ (k2_xboole_0 @ X40 @ X41))
% 0.67/0.86              = (k3_xboole_0 @ (k1_setfam_1 @ X40) @ (k1_setfam_1 @ X41)))
% 0.67/0.86          | ((X41) = (k1_xboole_0)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.67/0.86  thf('11', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.67/0.86            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.67/0.86          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.67/0.86          | ((X1) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['9', '10'])).
% 0.67/0.86  thf('12', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.67/0.86            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.67/0.86          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.67/0.86          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup+', [status(thm)], ['8', '11'])).
% 0.67/0.86  thf('13', plain, (![X42 : $i]: ((k1_setfam_1 @ (k1_tarski @ X42)) = (X42))),
% 0.67/0.86      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.67/0.86  thf('14', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.67/0.86          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.67/0.86          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.67/0.86      inference('demod', [status(thm)], ['12', '13'])).
% 0.67/0.86  thf(t12_setfam_1, conjecture,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i,B:$i]:
% 0.67/0.86        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.67/0.86  thf('15', plain,
% 0.67/0.86      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.67/0.86         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('16', plain,
% 0.67/0.86      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.67/0.86        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.67/0.86        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.86  thf('17', plain,
% 0.67/0.86      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.67/0.86        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.67/0.86      inference('simplify', [status(thm)], ['16'])).
% 0.67/0.86  thf(t16_zfmisc_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.67/0.86          ( ( A ) = ( B ) ) ) ))).
% 0.67/0.86  thf('18', plain,
% 0.67/0.86      (![X38 : $i, X39 : $i]:
% 0.67/0.86         (~ (r1_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X39))
% 0.67/0.86          | ((X38) != (X39)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.67/0.86  thf('19', plain,
% 0.67/0.86      (![X39 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X39))),
% 0.67/0.86      inference('simplify', [status(thm)], ['18'])).
% 0.67/0.86  thf('20', plain,
% 0.67/0.86      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.67/0.86        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['17', '19'])).
% 0.67/0.86  thf(t3_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.67/0.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.86            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.67/0.86  thf('21', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.86  thf(t17_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.86  thf('22', plain,
% 0.67/0.86      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.67/0.86      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.86  thf(t2_boole, axiom,
% 0.67/0.86    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.67/0.86  thf('23', plain,
% 0.67/0.86      (![X13 : $i]: ((k3_xboole_0 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.86      inference('cnf', [status(esa)], [t2_boole])).
% 0.67/0.86  thf('24', plain,
% 0.67/0.86      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.67/0.86      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.67/0.86  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.86      inference('sup+', [status(thm)], ['23', '24'])).
% 0.67/0.86  thf(d10_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.86  thf('26', plain,
% 0.67/0.86      (![X8 : $i, X10 : $i]:
% 0.67/0.86         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.67/0.86      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.86  thf('27', plain,
% 0.67/0.86      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.86  thf('28', plain,
% 0.67/0.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['22', '27'])).
% 0.67/0.86  thf(t4_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.86            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.67/0.86  thf('29', plain,
% 0.67/0.86      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.67/0.86          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.67/0.86  thf('30', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.86  thf(t48_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.86  thf('31', plain,
% 0.67/0.86      (![X16 : $i, X17 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.67/0.86           = (k3_xboole_0 @ X16 @ X17))),
% 0.67/0.86      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.86  thf('32', plain,
% 0.67/0.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['22', '27'])).
% 0.67/0.86  thf(t47_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.67/0.86  thf('33', plain,
% 0.67/0.86      (![X14 : $i, X15 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.67/0.86           = (k4_xboole_0 @ X14 @ X15))),
% 0.67/0.86      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.67/0.86  thf('34', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.86           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['32', '33'])).
% 0.67/0.86  thf('35', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.86           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.67/0.86      inference('sup+', [status(thm)], ['31', '34'])).
% 0.67/0.86  thf('36', plain,
% 0.67/0.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['22', '27'])).
% 0.67/0.86  thf('37', plain,
% 0.67/0.86      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.67/0.86      inference('demod', [status(thm)], ['35', '36'])).
% 0.67/0.86  thf(t83_xboole_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.86  thf('38', plain,
% 0.67/0.86      (![X18 : $i, X20 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.86  thf('39', plain,
% 0.67/0.86      ((((k1_xboole_0) != (k1_xboole_0))
% 0.67/0.86        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.86  thf('40', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.67/0.86      inference('simplify', [status(thm)], ['39'])).
% 0.67/0.86  thf('41', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.67/0.86      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.86  thf('42', plain,
% 0.67/0.86      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.67/0.86          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.67/0.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.67/0.86  thf('43', plain,
% 0.67/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.67/0.86          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['41', '42'])).
% 0.67/0.86  thf('44', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (r1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0)),
% 0.67/0.86      inference('sup-', [status(thm)], ['40', '43'])).
% 0.67/0.86  thf('45', plain,
% 0.67/0.86      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.67/0.86      inference('sup-', [status(thm)], ['22', '27'])).
% 0.67/0.86  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('47', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.67/0.86      inference('demod', [status(thm)], ['30', '46'])).
% 0.67/0.86  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.67/0.86      inference('sup-', [status(thm)], ['21', '47'])).
% 0.67/0.86  thf('49', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.67/0.86      inference('demod', [status(thm)], ['20', '48'])).
% 0.67/0.86  thf('50', plain,
% 0.67/0.86      (![X39 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X39) @ (k1_tarski @ X39))),
% 0.67/0.86      inference('simplify', [status(thm)], ['18'])).
% 0.67/0.86  thf('51', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.67/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.86  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.67/0.86      inference('demod', [status(thm)], ['20', '48'])).
% 0.67/0.86  thf('53', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('54', plain, ($false),
% 0.67/0.86      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
