%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cbyjLwyuhB

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 (  91 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  737 ( 866 expanded)
%              Number of equality atoms :   60 (  73 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
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

thf('5',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X55
       != ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      | ( ( k1_relat_1 @ X55 )
        = ( k2_tarski @ X51 @ X53 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('6',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
        = ( k2_tarski @ X51 @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X47 @ X48 ) @ ( k4_tarski @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('8',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      = ( k2_tarski @ X51 @ X53 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X46: $i] :
      ( ( ( k3_relat_1 @ X46 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X46 ) @ ( k2_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ( X55
       != ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      | ( ( k2_relat_1 @ X55 )
        = ( k2_tarski @ X52 @ X54 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('16',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
        = ( k2_tarski @ X52 @ X54 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X47 @ X48 ) @ ( k4_tarski @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('18',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X51 @ X52 ) @ ( k4_tarski @ X53 @ X54 ) ) )
      = ( k2_tarski @ X52 @ X54 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X47 @ X48 ) @ ( k4_tarski @ X49 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['13','21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('29',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k6_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cbyjLwyuhB
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 175 iterations in 0.075s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.22/0.53                                           $i > $i).
% 0.22/0.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.53  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(t32_relat_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.22/0.53       ( k2_tarski @ A @ B ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.22/0.53          ( k2_tarski @ A @ B ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.22/0.53         != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t70_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf(t69_enumset1, axiom,
% 0.22/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.53  thf('2', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf(t24_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ E ) =>
% 0.22/0.53       ( ( ( E ) =
% 0.22/0.53           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.22/0.53         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.22/0.53           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.22/0.53         (((X55)
% 0.22/0.53            != (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53          | ((k1_relat_1 @ X55) = (k2_tarski @ X51 @ X53))
% 0.22/0.53          | ~ (v1_relat_1 @ X55))),
% 0.22/0.53      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ 
% 0.22/0.53             (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53          | ((k1_relat_1 @ 
% 0.22/0.53              (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53              = (k2_tarski @ X51 @ X53)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.53  thf(fc7_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( v1_relat_1 @
% 0.22/0.53       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.53         (v1_relat_1 @ 
% 0.22/0.53          (k2_tarski @ (k4_tarski @ X47 @ X48) @ (k4_tarski @ X49 @ X50)))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.53         ((k1_relat_1 @ 
% 0.22/0.53           (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53           = (k2_tarski @ X51 @ X53))),
% 0.22/0.53      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.53           = (k2_tarski @ X1 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['4', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf(d6_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ( k3_relat_1 @ A ) =
% 0.22/0.53         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X46 : $i]:
% 0.22/0.53         (((k3_relat_1 @ X46)
% 0.22/0.53            = (k2_xboole_0 @ (k1_relat_1 @ X46) @ (k2_relat_1 @ X46)))
% 0.22/0.53          | ~ (v1_relat_1 @ X46))),
% 0.22/0.53      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.53            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.22/0.53               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.22/0.53          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.22/0.53      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.22/0.53         (((X55)
% 0.22/0.53            != (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53          | ((k2_relat_1 @ X55) = (k2_tarski @ X52 @ X54))
% 0.22/0.53          | ~ (v1_relat_1 @ X55))),
% 0.22/0.53      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ 
% 0.22/0.53             (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53          | ((k2_relat_1 @ 
% 0.22/0.53              (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53              = (k2_tarski @ X52 @ X54)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.53         (v1_relat_1 @ 
% 0.22/0.53          (k2_tarski @ (k4_tarski @ X47 @ X48) @ (k4_tarski @ X49 @ X50)))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.22/0.53         ((k2_relat_1 @ 
% 0.22/0.53           (k2_tarski @ (k4_tarski @ X51 @ X52) @ (k4_tarski @ X53 @ X54)))
% 0.22/0.53           = (k2_tarski @ X52 @ X54))),
% 0.22/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.53  thf('19', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.22/0.53           = (k2_tarski @ X0 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['14', '18'])).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.22/0.53         (v1_relat_1 @ 
% 0.22/0.53          (k2_tarski @ (k4_tarski @ X47 @ X48) @ (k4_tarski @ X49 @ X50)))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.53           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('demod', [status(thm)], ['13', '21', '24'])).
% 0.22/0.53  thf('26', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['3', '25'])).
% 0.22/0.53  thf(t71_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 0.22/0.53           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.53  thf(t72_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25)
% 0.22/0.53           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.53  thf(t75_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.53     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.53       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.22/0.53         ((k6_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 0.22/0.53           = (k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 0.22/0.53      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.22/0.53  thf(t74_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.53     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.53       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.53         ((k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.22/0.53           = (k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.22/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.53         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.53           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.53      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.53         ((k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 0.22/0.53           = (k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 0.22/0.53      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.53  thf(t68_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.22/0.53     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.22/0.53       ( k2_xboole_0 @
% 0.22/0.53         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.22/0.53         X15 : $i]:
% 0.22/0.53         ((k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.22/0.53           = (k2_xboole_0 @ 
% 0.22/0.53              (k5_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14) @ 
% 0.22/0.53              (k1_tarski @ X15)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.53         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.22/0.53           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.53              (k1_tarski @ X6)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.53           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.53              (k1_tarski @ X0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['31', '34'])).
% 0.22/0.53  thf(t73_enumset1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.53     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.53       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.22/0.53           = (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.22/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.22/0.53           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.53              (k1_tarski @ X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.22/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.53              (k1_tarski @ X4)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['28', '37'])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.53         ((k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30)
% 0.22/0.53           = (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 0.22/0.53      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4)
% 0.22/0.53           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.53              (k1_tarski @ X4)))),
% 0.22/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.22/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['27', '40'])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.53         ((k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25)
% 0.22/0.53           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X2 @ X1 @ X0 @ X3)
% 0.22/0.53           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.22/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.53         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 0.22/0.53           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 0.22/0.53      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.53           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.22/0.53      inference('demod', [status(thm)], ['26', '43', '44'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i]:
% 0.22/0.53         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.53      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.53  thf('47', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['0', '45', '46'])).
% 0.22/0.53  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
