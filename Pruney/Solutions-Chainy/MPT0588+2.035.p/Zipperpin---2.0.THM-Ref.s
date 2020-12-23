%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bceDDtCW0t

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:34 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   80 (  88 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  694 ( 774 expanded)
%              Number of equality atoms :   57 (  65 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X53 @ X54 ) ) @ ( k1_relat_1 @ X53 ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X55 ) @ X56 )
      | ( ( k7_relat_1 @ X55 @ X56 )
        = X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) @ X52 )
        = ( k7_relat_1 @ X50 @ ( k3_xboole_0 @ X51 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_relat_1 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t192_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k7_relat_1 @ B @ A )
          = ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_relat_1])).

thf('8',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30 )
      = ( k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k6_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 )
      = ( k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      = ( k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 ) @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_enumset1 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_enumset1 @ X19 @ X19 @ X20 @ X21 )
      = ( k1_enumset1 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X46 @ X47 ) )
      = ( k3_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bceDDtCW0t
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.63/1.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.63/1.82  % Solved by: fo/fo7.sh
% 1.63/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.63/1.82  % done 1544 iterations in 1.372s
% 1.63/1.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.63/1.82  % SZS output start Refutation
% 1.63/1.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.63/1.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.63/1.82  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.63/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.63/1.82  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.63/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.63/1.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.63/1.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.63/1.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.63/1.82  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.63/1.82  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.63/1.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.63/1.82  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.63/1.82                                           $i > $i).
% 1.63/1.82  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.63/1.82  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.63/1.82  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.63/1.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.63/1.82  thf(t89_relat_1, axiom,
% 1.63/1.82    (![A:$i,B:$i]:
% 1.63/1.82     ( ( v1_relat_1 @ B ) =>
% 1.63/1.82       ( r1_tarski @
% 1.63/1.82         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 1.63/1.82  thf('0', plain,
% 1.63/1.82      (![X53 : $i, X54 : $i]:
% 1.63/1.82         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X53 @ X54)) @ 
% 1.63/1.82           (k1_relat_1 @ X53))
% 1.63/1.82          | ~ (v1_relat_1 @ X53))),
% 1.63/1.82      inference('cnf', [status(esa)], [t89_relat_1])).
% 1.63/1.82  thf(t97_relat_1, axiom,
% 1.63/1.82    (![A:$i,B:$i]:
% 1.63/1.82     ( ( v1_relat_1 @ B ) =>
% 1.63/1.82       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.63/1.82         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 1.63/1.82  thf('1', plain,
% 1.63/1.82      (![X55 : $i, X56 : $i]:
% 1.63/1.82         (~ (r1_tarski @ (k1_relat_1 @ X55) @ X56)
% 1.63/1.82          | ((k7_relat_1 @ X55 @ X56) = (X55))
% 1.63/1.82          | ~ (v1_relat_1 @ X55))),
% 1.63/1.82      inference('cnf', [status(esa)], [t97_relat_1])).
% 1.63/1.82  thf('2', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         (~ (v1_relat_1 @ X0)
% 1.63/1.82          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 1.63/1.82          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.63/1.82              = (k7_relat_1 @ X0 @ X1)))),
% 1.63/1.82      inference('sup-', [status(thm)], ['0', '1'])).
% 1.63/1.82  thf(dt_k7_relat_1, axiom,
% 1.63/1.82    (![A:$i,B:$i]:
% 1.63/1.82     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 1.63/1.82  thf('3', plain,
% 1.63/1.82      (![X48 : $i, X49 : $i]:
% 1.63/1.82         (~ (v1_relat_1 @ X48) | (v1_relat_1 @ (k7_relat_1 @ X48 @ X49)))),
% 1.63/1.82      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 1.63/1.82  thf('4', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 1.63/1.82            = (k7_relat_1 @ X0 @ X1))
% 1.63/1.82          | ~ (v1_relat_1 @ X0))),
% 1.63/1.82      inference('clc', [status(thm)], ['2', '3'])).
% 1.63/1.82  thf(t100_relat_1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i]:
% 1.63/1.82     ( ( v1_relat_1 @ C ) =>
% 1.63/1.82       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 1.63/1.82         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 1.63/1.82  thf('5', plain,
% 1.63/1.82      (![X50 : $i, X51 : $i, X52 : $i]:
% 1.63/1.82         (((k7_relat_1 @ (k7_relat_1 @ X50 @ X51) @ X52)
% 1.63/1.82            = (k7_relat_1 @ X50 @ (k3_xboole_0 @ X51 @ X52)))
% 1.63/1.82          | ~ (v1_relat_1 @ X50))),
% 1.63/1.82      inference('cnf', [status(esa)], [t100_relat_1])).
% 1.63/1.82  thf('6', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         (((k7_relat_1 @ X1 @ X0)
% 1.63/1.82            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 1.63/1.82          | ~ (v1_relat_1 @ X1)
% 1.63/1.82          | ~ (v1_relat_1 @ X1))),
% 1.63/1.82      inference('sup+', [status(thm)], ['4', '5'])).
% 1.63/1.82  thf('7', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         (~ (v1_relat_1 @ X1)
% 1.63/1.82          | ((k7_relat_1 @ X1 @ X0)
% 1.63/1.82              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))))),
% 1.63/1.82      inference('simplify', [status(thm)], ['6'])).
% 1.63/1.82  thf(t192_relat_1, conjecture,
% 1.63/1.82    (![A:$i,B:$i]:
% 1.63/1.82     ( ( v1_relat_1 @ B ) =>
% 1.63/1.82       ( ( k7_relat_1 @ B @ A ) =
% 1.63/1.82         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 1.63/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.63/1.82    (~( ![A:$i,B:$i]:
% 1.63/1.82        ( ( v1_relat_1 @ B ) =>
% 1.63/1.82          ( ( k7_relat_1 @ B @ A ) =
% 1.63/1.82            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 1.63/1.82    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 1.63/1.82  thf('8', plain,
% 1.63/1.82      (((k7_relat_1 @ sk_B @ sk_A)
% 1.63/1.82         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 1.63/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.82  thf(t71_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i]:
% 1.63/1.82     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.63/1.82  thf('9', plain,
% 1.63/1.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.63/1.82           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.63/1.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.63/1.82  thf(t125_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i]:
% 1.63/1.82     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 1.63/1.82  thf('10', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 1.63/1.82      inference('cnf', [status(esa)], [t125_enumset1])).
% 1.63/1.82  thf('11', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['9', '10'])).
% 1.63/1.82  thf(t72_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i]:
% 1.63/1.82     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.63/1.82  thf('12', plain,
% 1.63/1.82      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.63/1.82         ((k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25)
% 1.63/1.82           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 1.63/1.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.63/1.82  thf('13', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.82         ((k3_enumset1 @ X0 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.63/1.82  thf(t73_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.63/1.82     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.63/1.82       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.63/1.82  thf('14', plain,
% 1.63/1.82      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.63/1.82         ((k4_enumset1 @ X26 @ X26 @ X27 @ X28 @ X29 @ X30)
% 1.63/1.82           = (k3_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30))),
% 1.63/1.82      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.63/1.82  thf('15', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.82         ((k4_enumset1 @ X0 @ X0 @ X0 @ X1 @ X2 @ X2)
% 1.63/1.82           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['13', '14'])).
% 1.63/1.82  thf(t70_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.63/1.82  thf('16', plain,
% 1.63/1.82      (![X17 : $i, X18 : $i]:
% 1.63/1.82         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.63/1.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.63/1.82  thf('17', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         ((k4_enumset1 @ X1 @ X1 @ X1 @ X0 @ X0 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.63/1.82      inference('sup+', [status(thm)], ['15', '16'])).
% 1.63/1.82  thf(t75_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.63/1.82     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.63/1.82       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.63/1.82  thf('18', plain,
% 1.63/1.82      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.63/1.82         ((k6_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43)
% 1.63/1.82           = (k5_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43))),
% 1.63/1.82      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.63/1.82  thf(t74_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.63/1.82     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.63/1.82       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.63/1.82  thf('19', plain,
% 1.63/1.82      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.63/1.82         ((k5_enumset1 @ X31 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 1.63/1.82           = (k4_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 1.63/1.82      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.63/1.82  thf('20', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.63/1.82         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.63/1.82           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['18', '19'])).
% 1.63/1.82  thf('21', plain,
% 1.63/1.82      (![X17 : $i, X18 : $i]:
% 1.63/1.82         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.63/1.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.63/1.82  thf(t69_enumset1, axiom,
% 1.63/1.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.63/1.82  thf('22', plain,
% 1.63/1.82      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 1.63/1.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.63/1.82  thf('23', plain,
% 1.63/1.82      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['21', '22'])).
% 1.63/1.82  thf(t66_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.63/1.82     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.63/1.82       ( k2_xboole_0 @
% 1.63/1.82         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 1.63/1.82  thf('24', plain,
% 1.63/1.82      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 1.63/1.82         X15 : $i]:
% 1.63/1.82         ((k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 1.63/1.82           = (k2_xboole_0 @ (k3_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12) @ 
% 1.63/1.82              (k1_enumset1 @ X13 @ X14 @ X15)))),
% 1.63/1.82      inference('cnf', [status(esa)], [t66_enumset1])).
% 1.63/1.82  thf('25', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.63/1.82         ((k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 1.63/1.82           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.63/1.82              (k1_tarski @ X0)))),
% 1.63/1.82      inference('sup+', [status(thm)], ['23', '24'])).
% 1.63/1.82  thf('26', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.63/1.82         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 1.63/1.82           = (k2_xboole_0 @ (k3_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1) @ 
% 1.63/1.82              (k1_tarski @ X0)))),
% 1.63/1.82      inference('sup+', [status(thm)], ['20', '25'])).
% 1.63/1.82  thf('27', plain,
% 1.63/1.82      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.63/1.82         ((k3_enumset1 @ X22 @ X22 @ X23 @ X24 @ X25)
% 1.63/1.82           = (k2_enumset1 @ X22 @ X23 @ X24 @ X25))),
% 1.63/1.82      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.63/1.82  thf('28', plain,
% 1.63/1.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.63/1.82           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.63/1.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.63/1.82  thf('29', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.63/1.82         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['27', '28'])).
% 1.63/1.82  thf(t46_enumset1, axiom,
% 1.63/1.82    (![A:$i,B:$i,C:$i,D:$i]:
% 1.63/1.82     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.63/1.82       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 1.63/1.82  thf('30', plain,
% 1.63/1.82      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X4 @ X5 @ X6 @ X7)
% 1.63/1.82           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X5 @ X6) @ (k1_tarski @ X7)))),
% 1.63/1.82      inference('cnf', [status(esa)], [t46_enumset1])).
% 1.63/1.82  thf('31', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.63/1.82         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 1.63/1.82           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 1.63/1.82      inference('demod', [status(thm)], ['26', '29', '30'])).
% 1.63/1.82  thf('32', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         ((k2_tarski @ X1 @ X0) = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 1.63/1.82      inference('sup+', [status(thm)], ['17', '31'])).
% 1.63/1.82  thf('33', plain,
% 1.63/1.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.63/1.82         ((k2_enumset1 @ X19 @ X19 @ X20 @ X21)
% 1.63/1.82           = (k1_enumset1 @ X19 @ X20 @ X21))),
% 1.63/1.82      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.63/1.82  thf('34', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.63/1.82      inference('demod', [status(thm)], ['32', '33'])).
% 1.63/1.82  thf('35', plain,
% 1.63/1.82      (![X17 : $i, X18 : $i]:
% 1.63/1.82         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 1.63/1.82      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.63/1.82  thf(t12_setfam_1, axiom,
% 1.63/1.82    (![A:$i,B:$i]:
% 1.63/1.82     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.63/1.82  thf('36', plain,
% 1.63/1.82      (![X46 : $i, X47 : $i]:
% 1.63/1.82         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.63/1.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.63/1.82  thf('37', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 1.63/1.82           = (k3_xboole_0 @ X1 @ X0))),
% 1.63/1.82      inference('sup+', [status(thm)], ['35', '36'])).
% 1.63/1.82  thf('38', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]:
% 1.63/1.82         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.63/1.82      inference('sup+', [status(thm)], ['34', '37'])).
% 1.63/1.82  thf('39', plain,
% 1.63/1.82      (![X46 : $i, X47 : $i]:
% 1.63/1.82         ((k1_setfam_1 @ (k2_tarski @ X46 @ X47)) = (k3_xboole_0 @ X46 @ X47))),
% 1.63/1.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.63/1.82  thf('40', plain,
% 1.63/1.82      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.63/1.82      inference('sup+', [status(thm)], ['38', '39'])).
% 1.63/1.82  thf('41', plain,
% 1.63/1.82      (((k7_relat_1 @ sk_B @ sk_A)
% 1.63/1.82         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 1.63/1.82      inference('demod', [status(thm)], ['8', '40'])).
% 1.63/1.82  thf('42', plain,
% 1.63/1.82      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 1.63/1.82        | ~ (v1_relat_1 @ sk_B))),
% 1.63/1.82      inference('sup-', [status(thm)], ['7', '41'])).
% 1.63/1.82  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 1.63/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.63/1.82  thf('44', plain,
% 1.63/1.82      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 1.63/1.82      inference('demod', [status(thm)], ['42', '43'])).
% 1.63/1.82  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 1.63/1.82  
% 1.63/1.82  % SZS output end Refutation
% 1.63/1.82  
% 1.66/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
