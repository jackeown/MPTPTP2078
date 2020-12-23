%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pLBfsPJC3E

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 144 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  559 (1275 expanded)
%              Number of equality atoms :   50 ( 117 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ ( k2_tarski @ X31 @ X34 ) )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X31: $i,X34: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X31 @ X34 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t105_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ( ( k4_xboole_0 @ B @ A )
          = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('9',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ ( k2_tarski @ X31 @ X34 ) )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('14',plain,(
    ! [X31: $i,X34: $i] :
      ( r1_tarski @ ( k1_tarski @ X31 ) @ ( k2_tarski @ X31 @ X34 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t87_enumset1,axiom,(
    ! [A: $i] :
      ( ( k3_enumset1 @ A @ A @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X28: $i] :
      ( ( k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t87_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19 )
      = ( k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X20 @ X21 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t65_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X8 @ X9 @ X10 ) @ ( k2_enumset1 @ X11 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t65_enumset1])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t105_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ~ ( r2_xboole_0 @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( r2_xboole_0 @ ( k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf(t81_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( r2_xboole_0 @ ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ~ ( r2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_tarski @ X4 @ X4 ) ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    ! [X31: $i,X34: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X31 @ X34 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( r2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(t95_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_enumset1 @ X29 @ X29 @ X29 @ X29 @ X29 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t95_enumset1])).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 )
      = ( k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t81_enumset1])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X29 @ X29 @ X29 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ~ ( r2_xboole_0 @ ( k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('46',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pLBfsPJC3E
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:59:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 101 iterations in 0.030s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.21/0.50                                           $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(t50_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(l45_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.50            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((r1_tarski @ X33 @ (k2_tarski @ X31 @ X34))
% 0.21/0.50          | ((X33) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X31 : $i, X34 : $i]:
% 0.21/0.50         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X31 @ X34))),
% 0.21/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.50  thf(d8_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.50       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_xboole_0) = (k2_tarski @ X1 @ X0))
% 0.21/0.50          | (r2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t46_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(t105_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.21/0.50          ( ( k4_xboole_0 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_xboole_0 @ X3 @ X4)
% 0.21/0.50          | ((k4_xboole_0 @ X4 @ X3) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50        | ~ (r2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.50  thf('11', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.50  thf('12', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 0.21/0.50      inference('demod', [status(thm)], ['0', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.21/0.50         ((r1_tarski @ X33 @ (k2_tarski @ X31 @ X34))
% 0.21/0.50          | ((X33) != (k1_tarski @ X31)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X31 : $i, X34 : $i]:
% 0.21/0.50         (r1_tarski @ (k1_tarski @ X31) @ (k2_tarski @ X31 @ X34))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_tarski @ X1) = (k2_tarski @ X1 @ X0))
% 0.21/0.50          | (r2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf(t87_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k3_enumset1 @ A @ A @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X28 : $i]:
% 0.21/0.50         ((k3_enumset1 @ X28 @ X28 @ X28 @ X28 @ X28) = (k1_tarski @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [t87_enumset1])).
% 0.21/0.50  thf(t73_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.21/0.50       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         ((k4_enumset1 @ X15 @ X15 @ X16 @ X17 @ X18 @ X19)
% 0.21/0.50           = (k3_enumset1 @ X15 @ X16 @ X17 @ X18 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.21/0.50  thf(t77_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i]:
% 0.21/0.50         ((k2_enumset1 @ X20 @ X20 @ X20 @ X21) = (k2_tarski @ X20 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.21/0.50  thf(t65_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.50     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.21/0.50       ( k2_xboole_0 @
% 0.21/0.50         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.21/0.50         X14 : $i]:
% 0.21/0.50         ((k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.50           = (k2_xboole_0 @ (k2_enumset1 @ X7 @ X8 @ X9 @ X10) @ 
% 0.21/0.50              (k2_enumset1 @ X11 @ X12 @ X13 @ X14)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t65_enumset1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_xboole_0 @ X3 @ X4)
% 0.21/0.50          | ((k4_xboole_0 @ X4 @ X3) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t105_xboole_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.50          | ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ~ (r2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)),
% 0.21/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ 
% 0.21/0.50            (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.21/0.50            (k2_enumset1 @ X7 @ X6 @ X5 @ X4))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ 
% 0.21/0.50            (k6_enumset1 @ X1 @ X1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.50            (k2_tarski @ X1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.50  thf(t81_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( k6_enumset1 @ A @ A @ A @ B @ C @ D @ E @ F ) =
% 0.21/0.50       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         ((k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.50           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ (k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.50            (k2_tarski @ X1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.21/0.50            (k2_tarski @ X4 @ X4))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]: ~ (r2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '29'])).
% 0.21/0.50  thf('31', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '30'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X31 : $i, X34 : $i]:
% 0.21/0.50         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X31 @ X34))),
% 0.21/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.50  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X2 : $i]:
% 0.21/0.50         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.21/0.50          | (r2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.50  thf(t95_enumset1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k6_enumset1 @ A @ A @ A @ A @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         ((k6_enumset1 @ X29 @ X29 @ X29 @ X29 @ X29 @ X29 @ X29 @ X30)
% 0.21/0.50           = (k2_tarski @ X29 @ X30))),
% 0.21/0.50      inference('cnf', [status(esa)], [t95_enumset1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.50         ((k6_enumset1 @ X22 @ X22 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27)
% 0.21/0.50           = (k4_enumset1 @ X22 @ X23 @ X24 @ X25 @ X26 @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [t81_enumset1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X29 : $i, X30 : $i]:
% 0.21/0.50         ((k4_enumset1 @ X29 @ X29 @ X29 @ X29 @ X29 @ X30)
% 0.21/0.50           = (k2_tarski @ X29 @ X30))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ (k4_enumset1 @ X1 @ X0 @ X5 @ X4 @ X3 @ X2) @ 
% 0.21/0.50            (k2_tarski @ X1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.50  thf('42', plain, (![X0 : $i]: ((k1_tarski @ X0) = (k2_tarski @ X0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '30'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ~ (r2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain, (~ (r2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '43'])).
% 0.21/0.50  thf('45', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '44'])).
% 0.21/0.50  thf(t49_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X37 : $i, X38 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k1_tarski @ X37) @ X38) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '47'])).
% 0.21/0.50  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
