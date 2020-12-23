%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VI2c0ZSoF1

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:34 EST 2020

% Result     : Theorem 7.23s
% Output     : Refutation 7.23s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 106 expanded)
%              Number of leaves         :   33 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  817 (1014 expanded)
%              Number of equality atoms :   65 (  83 expanded)
%              Maximal formula depth    :   18 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t89_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X55 @ X56 ) ) @ ( k1_relat_1 @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t89_relat_1])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X57 ) @ X58 )
      | ( ( k7_relat_1 @ X57 @ X58 )
        = X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
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
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X50 @ X51 ) ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X52 @ X53 ) @ X54 )
        = ( k7_relat_1 @ X52 @ ( k3_xboole_0 @ X53 @ X54 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
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

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('15',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k6_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 )
      = ( k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( k5_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 )
      = ( k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ ( k1_enumset1 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_enumset1 @ X6 @ X5 @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 )
      = ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27 )
      = ( k2_enumset1 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t55_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t55_enumset1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X0 @ X0 @ X1 @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','34'])).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X21 @ X21 @ X22 @ X23 )
      = ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X2 @ X2 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','38','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X19 @ X19 @ X20 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X48 @ X49 ) )
      = ( k3_xboole_0 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','48'])).

thf('50',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k7_relat_1 @ sk_B @ sk_A )
 != ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VI2c0ZSoF1
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.23/7.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.23/7.43  % Solved by: fo/fo7.sh
% 7.23/7.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.23/7.43  % done 3478 iterations in 6.971s
% 7.23/7.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.23/7.43  % SZS output start Refutation
% 7.23/7.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.23/7.43  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 7.23/7.43  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 7.23/7.43  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 7.23/7.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.23/7.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.23/7.43  thf(sk_A_type, type, sk_A: $i).
% 7.23/7.43  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.23/7.43  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.23/7.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.23/7.43  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 7.23/7.43                                           $i > $i).
% 7.23/7.43  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 7.23/7.43  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.23/7.43  thf(sk_B_type, type, sk_B: $i).
% 7.23/7.43  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 7.23/7.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.23/7.43  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 7.23/7.43  thf(t89_relat_1, axiom,
% 7.23/7.43    (![A:$i,B:$i]:
% 7.23/7.43     ( ( v1_relat_1 @ B ) =>
% 7.23/7.43       ( r1_tarski @
% 7.23/7.43         ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ ( k1_relat_1 @ B ) ) ))).
% 7.23/7.43  thf('0', plain,
% 7.23/7.43      (![X55 : $i, X56 : $i]:
% 7.23/7.43         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X55 @ X56)) @ 
% 7.23/7.43           (k1_relat_1 @ X55))
% 7.23/7.43          | ~ (v1_relat_1 @ X55))),
% 7.23/7.43      inference('cnf', [status(esa)], [t89_relat_1])).
% 7.23/7.43  thf(t97_relat_1, axiom,
% 7.23/7.43    (![A:$i,B:$i]:
% 7.23/7.43     ( ( v1_relat_1 @ B ) =>
% 7.23/7.43       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 7.23/7.43         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 7.23/7.43  thf('1', plain,
% 7.23/7.43      (![X57 : $i, X58 : $i]:
% 7.23/7.43         (~ (r1_tarski @ (k1_relat_1 @ X57) @ X58)
% 7.23/7.43          | ((k7_relat_1 @ X57 @ X58) = (X57))
% 7.23/7.43          | ~ (v1_relat_1 @ X57))),
% 7.23/7.43      inference('cnf', [status(esa)], [t97_relat_1])).
% 7.23/7.43  thf('2', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         (~ (v1_relat_1 @ X0)
% 7.23/7.43          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 7.23/7.43          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 7.23/7.43              = (k7_relat_1 @ X0 @ X1)))),
% 7.23/7.43      inference('sup-', [status(thm)], ['0', '1'])).
% 7.23/7.43  thf(dt_k7_relat_1, axiom,
% 7.23/7.43    (![A:$i,B:$i]:
% 7.23/7.43     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 7.23/7.43  thf('3', plain,
% 7.23/7.43      (![X50 : $i, X51 : $i]:
% 7.23/7.43         (~ (v1_relat_1 @ X50) | (v1_relat_1 @ (k7_relat_1 @ X50 @ X51)))),
% 7.23/7.43      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 7.23/7.43  thf('4', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 7.23/7.43            = (k7_relat_1 @ X0 @ X1))
% 7.23/7.43          | ~ (v1_relat_1 @ X0))),
% 7.23/7.43      inference('clc', [status(thm)], ['2', '3'])).
% 7.23/7.43  thf(t100_relat_1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i]:
% 7.23/7.43     ( ( v1_relat_1 @ C ) =>
% 7.23/7.43       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 7.23/7.43         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 7.23/7.43  thf('5', plain,
% 7.23/7.43      (![X52 : $i, X53 : $i, X54 : $i]:
% 7.23/7.43         (((k7_relat_1 @ (k7_relat_1 @ X52 @ X53) @ X54)
% 7.23/7.43            = (k7_relat_1 @ X52 @ (k3_xboole_0 @ X53 @ X54)))
% 7.23/7.43          | ~ (v1_relat_1 @ X52))),
% 7.23/7.43      inference('cnf', [status(esa)], [t100_relat_1])).
% 7.23/7.43  thf('6', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         (((k7_relat_1 @ X1 @ X0)
% 7.23/7.43            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1))))
% 7.23/7.43          | ~ (v1_relat_1 @ X1)
% 7.23/7.43          | ~ (v1_relat_1 @ X1))),
% 7.23/7.43      inference('sup+', [status(thm)], ['4', '5'])).
% 7.23/7.43  thf('7', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         (~ (v1_relat_1 @ X1)
% 7.23/7.43          | ((k7_relat_1 @ X1 @ X0)
% 7.23/7.43              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ (k1_relat_1 @ X1)))))),
% 7.23/7.43      inference('simplify', [status(thm)], ['6'])).
% 7.23/7.43  thf(t192_relat_1, conjecture,
% 7.23/7.43    (![A:$i,B:$i]:
% 7.23/7.43     ( ( v1_relat_1 @ B ) =>
% 7.23/7.43       ( ( k7_relat_1 @ B @ A ) =
% 7.23/7.43         ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 7.23/7.43  thf(zf_stmt_0, negated_conjecture,
% 7.23/7.43    (~( ![A:$i,B:$i]:
% 7.23/7.43        ( ( v1_relat_1 @ B ) =>
% 7.23/7.43          ( ( k7_relat_1 @ B @ A ) =
% 7.23/7.43            ( k7_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )),
% 7.23/7.43    inference('cnf.neg', [status(esa)], [t192_relat_1])).
% 7.23/7.43  thf('8', plain,
% 7.23/7.43      (((k7_relat_1 @ sk_B @ sk_A)
% 7.23/7.43         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 7.23/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.23/7.43  thf(t73_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 7.23/7.43     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 7.23/7.43       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 7.23/7.43  thf('9', plain,
% 7.23/7.43      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X28 @ X28 @ X29 @ X30 @ X31 @ X32)
% 7.23/7.43           = (k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32))),
% 7.23/7.43      inference('cnf', [status(esa)], [t73_enumset1])).
% 7.23/7.43  thf(t72_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i]:
% 7.23/7.43     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 7.23/7.43  thf('10', plain,
% 7.23/7.43      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 7.23/7.43         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 7.23/7.43           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 7.23/7.43      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.23/7.43  thf('11', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['9', '10'])).
% 7.23/7.43  thf(t70_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 7.23/7.43  thf('12', plain,
% 7.23/7.43      (![X19 : $i, X20 : $i]:
% 7.23/7.43         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 7.23/7.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.23/7.43  thf(t69_enumset1, axiom,
% 7.23/7.43    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 7.23/7.43  thf('13', plain,
% 7.23/7.43      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 7.23/7.43      inference('cnf', [status(esa)], [t69_enumset1])).
% 7.23/7.43  thf('14', plain,
% 7.23/7.43      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['12', '13'])).
% 7.23/7.43  thf(t75_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 7.23/7.43     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 7.23/7.43       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 7.23/7.43  thf('15', plain,
% 7.23/7.43      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 7.23/7.43         ((k6_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45)
% 7.23/7.43           = (k5_enumset1 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 @ X45))),
% 7.23/7.43      inference('cnf', [status(esa)], [t75_enumset1])).
% 7.23/7.43  thf(t74_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.23/7.43     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 7.23/7.43       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 7.23/7.43  thf('16', plain,
% 7.23/7.43      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 7.23/7.43         ((k5_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38)
% 7.23/7.43           = (k4_enumset1 @ X33 @ X34 @ X35 @ X36 @ X37 @ X38))),
% 7.23/7.43      inference('cnf', [status(esa)], [t74_enumset1])).
% 7.23/7.43  thf('17', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.23/7.43         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['15', '16'])).
% 7.23/7.43  thf('18', plain,
% 7.23/7.43      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 7.23/7.43         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 7.23/7.43           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 7.23/7.43      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.23/7.43  thf(t66_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 7.23/7.43     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 7.23/7.43       ( k2_xboole_0 @
% 7.23/7.43         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 7.23/7.43  thf('19', plain,
% 7.23/7.43      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 7.23/7.43         X17 : $i]:
% 7.23/7.43         ((k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 7.23/7.43           = (k2_xboole_0 @ (k3_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14) @ 
% 7.23/7.43              (k1_enumset1 @ X15 @ X16 @ X17)))),
% 7.23/7.43      inference('cnf', [status(esa)], [t66_enumset1])).
% 7.23/7.43  thf('20', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 7.23/7.43         ((k6_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X6 @ X5 @ X4)
% 7.23/7.43           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.23/7.43              (k1_enumset1 @ X6 @ X5 @ X4)))),
% 7.23/7.43      inference('sup+', [status(thm)], ['18', '19'])).
% 7.23/7.43  thf('21', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X5 @ X4 @ X3) @ 
% 7.23/7.43              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.23/7.43      inference('sup+', [status(thm)], ['17', '20'])).
% 7.23/7.43  thf(t71_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i]:
% 7.23/7.43     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 7.23/7.43  thf('22', plain,
% 7.23/7.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 7.23/7.43           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 7.23/7.43      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.23/7.43  thf('23', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 7.23/7.43              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 7.23/7.43      inference('demod', [status(thm)], ['21', '22'])).
% 7.23/7.43  thf('24', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 7.23/7.43           = (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 7.23/7.43      inference('sup+', [status(thm)], ['14', '23'])).
% 7.23/7.43  thf('25', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['9', '10'])).
% 7.23/7.43  thf(t125_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i]:
% 7.23/7.43     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 7.23/7.43  thf('26', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 7.23/7.43      inference('cnf', [status(esa)], [t125_enumset1])).
% 7.23/7.43  thf('27', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X0 @ X1 @ X2 @ X3)
% 7.23/7.43           = (k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['25', '26'])).
% 7.23/7.43  thf('28', plain,
% 7.23/7.43      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 7.23/7.43         ((k3_enumset1 @ X24 @ X24 @ X25 @ X26 @ X27)
% 7.23/7.43           = (k2_enumset1 @ X24 @ X25 @ X26 @ X27))),
% 7.23/7.43      inference('cnf', [status(esa)], [t72_enumset1])).
% 7.23/7.43  thf(t55_enumset1, axiom,
% 7.23/7.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.23/7.43     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 7.23/7.43       ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_tarski @ F ) ) ))).
% 7.23/7.43  thf('29', plain,
% 7.23/7.43      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8 @ X9)
% 7.23/7.43           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X5 @ X6 @ X7 @ X8) @ 
% 7.23/7.43              (k1_tarski @ X9)))),
% 7.23/7.43      inference('cnf', [status(esa)], [t55_enumset1])).
% 7.23/7.43  thf('30', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4)
% 7.23/7.43           = (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ 
% 7.23/7.43              (k1_tarski @ X4)))),
% 7.23/7.43      inference('sup+', [status(thm)], ['28', '29'])).
% 7.23/7.43  thf('31', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_xboole_0 @ (k2_enumset1 @ X0 @ X0 @ X1 @ X2) @ 
% 7.23/7.43              (k1_tarski @ X3)))),
% 7.23/7.43      inference('sup+', [status(thm)], ['27', '30'])).
% 7.23/7.43  thf('32', plain,
% 7.23/7.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 7.23/7.43           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 7.23/7.43      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.23/7.43  thf('33', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 7.23/7.43           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X1 @ X2) @ (k1_tarski @ X3)))),
% 7.23/7.43      inference('demod', [status(thm)], ['31', '32'])).
% 7.23/7.43  thf('34', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k4_enumset1 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 7.23/7.43           = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 7.23/7.43      inference('demod', [status(thm)], ['24', '33'])).
% 7.23/7.43  thf('35', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X1 @ X0 @ X0 @ X0) = (k2_enumset1 @ X0 @ X1 @ X1 @ X1))),
% 7.23/7.43      inference('sup+', [status(thm)], ['11', '34'])).
% 7.23/7.43  thf('36', plain,
% 7.23/7.43      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X21 @ X21 @ X22 @ X23)
% 7.23/7.43           = (k1_enumset1 @ X21 @ X22 @ X23))),
% 7.23/7.43      inference('cnf', [status(esa)], [t71_enumset1])).
% 7.23/7.43  thf('37', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) = (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 7.23/7.43      inference('cnf', [status(esa)], [t125_enumset1])).
% 7.23/7.43  thf('38', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['36', '37'])).
% 7.23/7.43  thf('39', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.23/7.43         ((k2_enumset1 @ X0 @ X1 @ X2 @ X2) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['36', '37'])).
% 7.23/7.43  thf('40', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         ((k1_enumset1 @ X0 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 7.23/7.43      inference('demod', [status(thm)], ['35', '38', '39'])).
% 7.23/7.43  thf('41', plain,
% 7.23/7.43      (![X19 : $i, X20 : $i]:
% 7.23/7.43         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 7.23/7.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.23/7.43  thf('42', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 7.23/7.43      inference('sup+', [status(thm)], ['40', '41'])).
% 7.23/7.43  thf('43', plain,
% 7.23/7.43      (![X19 : $i, X20 : $i]:
% 7.23/7.43         ((k1_enumset1 @ X19 @ X19 @ X20) = (k2_tarski @ X19 @ X20))),
% 7.23/7.43      inference('cnf', [status(esa)], [t70_enumset1])).
% 7.23/7.43  thf(t12_setfam_1, axiom,
% 7.23/7.43    (![A:$i,B:$i]:
% 7.23/7.43     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 7.23/7.43  thf('44', plain,
% 7.23/7.43      (![X48 : $i, X49 : $i]:
% 7.23/7.43         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 7.23/7.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.23/7.43  thf('45', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         ((k1_setfam_1 @ (k1_enumset1 @ X1 @ X1 @ X0))
% 7.23/7.43           = (k3_xboole_0 @ X1 @ X0))),
% 7.23/7.43      inference('sup+', [status(thm)], ['43', '44'])).
% 7.23/7.43  thf('46', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]:
% 7.23/7.43         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 7.23/7.43      inference('sup+', [status(thm)], ['42', '45'])).
% 7.23/7.43  thf('47', plain,
% 7.23/7.43      (![X48 : $i, X49 : $i]:
% 7.23/7.43         ((k1_setfam_1 @ (k2_tarski @ X48 @ X49)) = (k3_xboole_0 @ X48 @ X49))),
% 7.23/7.43      inference('cnf', [status(esa)], [t12_setfam_1])).
% 7.23/7.43  thf('48', plain,
% 7.23/7.43      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 7.23/7.43      inference('sup+', [status(thm)], ['46', '47'])).
% 7.23/7.43  thf('49', plain,
% 7.23/7.43      (((k7_relat_1 @ sk_B @ sk_A)
% 7.23/7.43         != (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_A @ (k1_relat_1 @ sk_B))))),
% 7.23/7.43      inference('demod', [status(thm)], ['8', '48'])).
% 7.23/7.43  thf('50', plain,
% 7.23/7.43      ((((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))
% 7.23/7.43        | ~ (v1_relat_1 @ sk_B))),
% 7.23/7.43      inference('sup-', [status(thm)], ['7', '49'])).
% 7.23/7.43  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 7.23/7.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.23/7.43  thf('52', plain,
% 7.23/7.43      (((k7_relat_1 @ sk_B @ sk_A) != (k7_relat_1 @ sk_B @ sk_A))),
% 7.23/7.43      inference('demod', [status(thm)], ['50', '51'])).
% 7.23/7.43  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 7.23/7.43  
% 7.23/7.43  % SZS output end Refutation
% 7.23/7.43  
% 7.23/7.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
