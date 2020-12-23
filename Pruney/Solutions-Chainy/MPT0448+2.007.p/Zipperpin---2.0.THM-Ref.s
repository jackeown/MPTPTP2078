%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T0AR7TzliR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 (  85 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  649 ( 762 expanded)
%              Number of equality atoms :   56 (  68 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t32_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( X54
       != ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      | ( ( k1_relat_1 @ X54 )
        = ( k2_tarski @ X50 @ X52 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('3',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
        = ( k2_tarski @ X50 @ X52 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      = ( k2_tarski @ X50 @ X52 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( X54
       != ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      | ( ( k2_relat_1 @ X54 )
        = ( k2_tarski @ X51 @ X53 ) )
      | ~ ( v1_relat_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('13',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
        = ( k2_tarski @ X51 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('15',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X50 @ X51 ) @ ( k4_tarski @ X52 @ X53 ) ) )
      = ( k2_tarski @ X51 @ X53 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X46 @ X47 ) @ ( k4_tarski @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','18','21'])).

thf('23',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','22'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k5_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X18 @ X18 @ X19 @ X20 )
      = ( k1_enumset1 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['23','42','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T0AR7TzliR
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:22:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 69 iterations in 0.048s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(t32_relat_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.20/0.51       ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.20/0.51          ( k2_tarski @ A @ B ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.20/0.51         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('1', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(t24_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ E ) =>
% 0.20/0.51       ( ( ( E ) =
% 0.20/0.51           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.20/0.51         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.20/0.51           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.20/0.51         (((X54)
% 0.20/0.51            != (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51          | ((k1_relat_1 @ X54) = (k2_tarski @ X50 @ X52))
% 0.20/0.51          | ~ (v1_relat_1 @ X54))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ 
% 0.20/0.51             (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51          | ((k1_relat_1 @ 
% 0.20/0.51              (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51              = (k2_tarski @ X50 @ X52)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.51  thf(fc7_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( v1_relat_1 @
% 0.20/0.51       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.51         (v1_relat_1 @ 
% 0.20/0.51          (k2_tarski @ (k4_tarski @ X46 @ X47) @ (k4_tarski @ X48 @ X49)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.51         ((k1_relat_1 @ 
% 0.20/0.51           (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51           = (k2_tarski @ X50 @ X52))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.51           = (k2_tarski @ X1 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '5'])).
% 0.20/0.51  thf('7', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(d6_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ( k3_relat_1 @ A ) =
% 0.20/0.51         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X45 : $i]:
% 0.20/0.51         (((k3_relat_1 @ X45)
% 0.20/0.51            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 0.20/0.51          | ~ (v1_relat_1 @ X45))),
% 0.20/0.51      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.20/0.51            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.20/0.51               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.20/0.51          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.20/0.51         (((X54)
% 0.20/0.51            != (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51          | ((k2_relat_1 @ X54) = (k2_tarski @ X51 @ X53))
% 0.20/0.51          | ~ (v1_relat_1 @ X54))),
% 0.20/0.51      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ 
% 0.20/0.51             (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51          | ((k2_relat_1 @ 
% 0.20/0.51              (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51              = (k2_tarski @ X51 @ X53)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.51         (v1_relat_1 @ 
% 0.20/0.51          (k2_tarski @ (k4_tarski @ X46 @ X47) @ (k4_tarski @ X48 @ X49)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.20/0.51         ((k2_relat_1 @ 
% 0.20/0.51           (k2_tarski @ (k4_tarski @ X50 @ X51) @ (k4_tarski @ X52 @ X53)))
% 0.20/0.51           = (k2_tarski @ X51 @ X53))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.51           = (k2_tarski @ X0 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['11', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.20/0.51         (v1_relat_1 @ 
% 0.20/0.51          (k2_tarski @ (k4_tarski @ X46 @ X47) @ (k4_tarski @ X48 @ X49)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['10', '18', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.51         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '22'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t71_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X18 @ X18 @ X19 @ X20)
% 0.20/0.51           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.51  thf(t74_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.51     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.20/0.51       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.51         ((k5_enumset1 @ X30 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.20/0.51           = (k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 0.20/0.51      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.20/0.51  thf(t73_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.51     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.20/0.51       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         ((k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.51           = (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.51           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         ((k4_enumset1 @ X25 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.20/0.51           = (k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.20/0.51  thf(t61_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.20/0.51     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.20/0.51       ( k2_xboole_0 @
% 0.20/0.51         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         ((k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6)
% 0.20/0.51           = (k2_xboole_0 @ (k4_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5) @ 
% 0.20/0.51              (k1_tarski @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.20/0.51           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.20/0.51              (k1_tarski @ X5)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.51           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.20/0.51              (k1_tarski @ X0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.51  thf(t72_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24)
% 0.20/0.51           = (k2_enumset1 @ X21 @ X22 @ X23 @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.20/0.51           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.20/0.51              (k1_tarski @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['27', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.51         ((k3_enumset1 @ X21 @ X21 @ X22 @ X23 @ X24)
% 0.20/0.51           = (k2_enumset1 @ X21 @ X22 @ X23 @ X24))),
% 0.20/0.51      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.20/0.51           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.20/0.51      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['26', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((k2_enumset1 @ X18 @ X18 @ X19 @ X20)
% 0.20/0.51           = (k1_enumset1 @ X18 @ X19 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf('44', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '42', '43'])).
% 0.20/0.51  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
