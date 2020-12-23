%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wADUEMZrU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 160 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :   15
%              Number of atoms          : 1000 (1890 expanded)
%              Number of equality atoms :   63 ( 143 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(t67_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k2_tarski @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t51_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ) )).

thf('22',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X21 ) @ ( k1_enumset1 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X6 )
      = ( k2_xboole_0 @ ( k2_tarski @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['23','36'])).

thf('38',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['0','37'])).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ ( k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t51_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X7 @ X6 ) @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k1_enumset1 @ sk_A @ sk_B @ sk_C ) @ ( k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_enumset1 @ X26 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X8 @ X9 @ X10 @ X11 ) @ ( k2_enumset1 @ X12 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k1_enumset1 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4wADUEMZrU
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 121 iterations in 0.155s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.36/0.62  thf(sk_H_type, type, sk_H: $i).
% 0.36/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.36/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.36/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.62  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.36/0.62                                           $i > $i).
% 0.36/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.63  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.36/0.63  thf(t67_enumset1, conjecture,
% 0.36/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.63       ( k2_xboole_0 @
% 0.36/0.63         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ))).
% 0.36/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.63        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.63          ( k2_xboole_0 @
% 0.36/0.63            ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k2_tarski @ G @ H ) ) ) )),
% 0.36/0.63    inference('cnf.neg', [status(esa)], [t67_enumset1])).
% 0.36/0.63  thf('0', plain,
% 0.36/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.63         != (k2_xboole_0 @ 
% 0.36/0.63             (k4_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.36/0.63             (k2_tarski @ sk_G @ sk_H)))),
% 0.36/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.63  thf(t42_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.36/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.36/0.63  thf('1', plain,
% 0.36/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.63         ((k1_enumset1 @ X18 @ X19 @ X20)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.36/0.63  thf(t41_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i]:
% 0.36/0.63     ( ( k2_tarski @ A @ B ) =
% 0.36/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.63  thf('2', plain,
% 0.36/0.63      (![X16 : $i, X17 : $i]:
% 0.36/0.63         ((k2_tarski @ X16 @ X17)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.63  thf('3', plain,
% 0.36/0.63      (![X16 : $i, X17 : $i]:
% 0.36/0.63         ((k2_tarski @ X16 @ X17)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.36/0.63  thf(t4_xboole_1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i]:
% 0.36/0.63     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.36/0.63       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.63  thf('4', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.63  thf('5', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.63  thf('6', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['2', '5'])).
% 0.36/0.63  thf('7', plain,
% 0.36/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.63         ((k1_enumset1 @ X18 @ X19 @ X20)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.36/0.63  thf('8', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.36/0.63           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.36/0.63  thf('9', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.63  thf('10', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('11', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.63              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['1', '10'])).
% 0.36/0.63  thf(t44_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.63     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.36/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.36/0.63  thf('12', plain,
% 0.36/0.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.63         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.36/0.63  thf('13', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.63  thf('14', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.36/0.63              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['12', '13'])).
% 0.36/0.63  thf(t47_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.63     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.36/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.36/0.63  thf('15', plain,
% 0.36/0.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.63         ((k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X25) @ 
% 0.36/0.63              (k2_enumset1 @ X26 @ X27 @ X28 @ X29)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.36/0.63  thf('16', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.36/0.63              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.63  thf('17', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.36/0.63           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.36/0.63      inference('demod', [status(thm)], ['11', '16'])).
% 0.36/0.63  thf('18', plain,
% 0.36/0.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.63         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.36/0.63  thf('19', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.63  thf('20', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.63  thf('21', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.63           (k2_tarski @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.36/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['17', '20'])).
% 0.36/0.63  thf(t51_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.36/0.63     ( ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) =
% 0.36/0.63       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k3_enumset1 @ B @ C @ D @ E @ F ) ) ))).
% 0.36/0.63  thf('22', plain,
% 0.36/0.63      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X30) @ 
% 0.36/0.63              (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.36/0.63  thf('23', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.63           = (k2_xboole_0 @ (k2_enumset1 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.63              (k2_tarski @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.63  thf('24', plain,
% 0.36/0.63      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.63         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X21) @ (k1_enumset1 @ X22 @ X23 @ X24)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.36/0.63  thf('25', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('26', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.36/0.63           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.63              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.63  thf('27', plain,
% 0.36/0.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.63         ((k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X25) @ 
% 0.36/0.63              (k2_enumset1 @ X26 @ X27 @ X28 @ X29)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.36/0.63  thf('28', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['3', '4'])).
% 0.36/0.63  thf('29', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.63           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.36/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.36/0.63  thf('30', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.36/0.63           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.63              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['24', '25'])).
% 0.36/0.63  thf('31', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.36/0.63           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X5) @ 
% 0.36/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.36/0.63  thf('32', plain,
% 0.36/0.63      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X30) @ 
% 0.36/0.63              (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.36/0.63  thf('33', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.63           = (k2_xboole_0 @ (k1_enumset1 @ X5 @ X4 @ X3) @ 
% 0.36/0.63              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.63  thf('34', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.63              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['26', '33'])).
% 0.36/0.63  thf('35', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.63  thf('36', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ X6)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X5 @ X4) @ 
% 0.36/0.63              (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X6)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['34', '35'])).
% 0.36/0.63  thf('37', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k4_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.36/0.63           (k2_tarski @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.63              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['23', '36'])).
% 0.36/0.63  thf('38', plain,
% 0.36/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.63         != (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 0.36/0.63             (k4_enumset1 @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.36/0.63      inference('demod', [status(thm)], ['0', '37'])).
% 0.36/0.63  thf('39', plain,
% 0.36/0.63      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.63         ((k4_enumset1 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X30) @ 
% 0.36/0.63              (k3_enumset1 @ X31 @ X32 @ X33 @ X34 @ X35)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t51_enumset1])).
% 0.36/0.63  thf('40', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('41', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.36/0.63           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X7 @ X6) @ 
% 0.36/0.63              (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['39', '40'])).
% 0.36/0.63  thf('42', plain,
% 0.36/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.63         != (k2_xboole_0 @ (k1_enumset1 @ sk_A @ sk_B @ sk_C) @ 
% 0.36/0.63             (k3_enumset1 @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)))),
% 0.36/0.63      inference('demod', [status(thm)], ['38', '41'])).
% 0.36/0.63  thf('43', plain,
% 0.36/0.63      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.36/0.63         ((k3_enumset1 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X25) @ 
% 0.36/0.63              (k2_enumset1 @ X26 @ X27 @ X28 @ X29)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.36/0.63  thf('44', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['8', '9'])).
% 0.36/0.63  thf('45', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.36/0.63           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.36/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['43', '44'])).
% 0.36/0.63  thf('46', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.36/0.63              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.36/0.63  thf('47', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.36/0.63           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.36/0.63              (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.36/0.63               (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))))),
% 0.36/0.63      inference('sup+', [status(thm)], ['45', '46'])).
% 0.36/0.63  thf(l75_enumset1, axiom,
% 0.36/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.36/0.63     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.36/0.63       ( k2_xboole_0 @
% 0.36/0.63         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.36/0.63  thf('48', plain,
% 0.36/0.63      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.36/0.63         X15 : $i]:
% 0.36/0.63         ((k6_enumset1 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15)
% 0.36/0.63           = (k2_xboole_0 @ (k2_enumset1 @ X8 @ X9 @ X10 @ X11) @ 
% 0.36/0.63              (k2_enumset1 @ X12 @ X13 @ X14 @ X15)))),
% 0.36/0.63      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.36/0.63  thf('49', plain,
% 0.36/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.63         ((k1_enumset1 @ X18 @ X19 @ X20)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.36/0.63  thf('50', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.36/0.63           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 0.36/0.63      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.36/0.63  thf('51', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.63         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.36/0.63           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.36/0.63              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.36/0.63      inference('sup+', [status(thm)], ['49', '50'])).
% 0.36/0.63  thf('52', plain,
% 0.36/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.63         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.36/0.63           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.36/0.63              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.36/0.63      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.36/0.63  thf('53', plain,
% 0.36/0.63      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.36/0.63         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.36/0.63             sk_H))),
% 0.36/0.63      inference('demod', [status(thm)], ['42', '52'])).
% 0.36/0.63  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.36/0.63  
% 0.36/0.63  % SZS output end Refutation
% 0.36/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
