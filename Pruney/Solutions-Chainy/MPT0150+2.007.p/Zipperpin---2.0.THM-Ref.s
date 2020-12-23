%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UsJDLz6sGH

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:27:17 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 132 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  741 (1507 expanded)
%              Number of equality atoms :   48 ( 116 expanded)
%              Maximal formula depth    :   19 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t66_enumset1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
        = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_enumset1])).

thf('0',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k2_xboole_0 @ ( k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_enumset1 @ sk_F @ sk_G @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ X5 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X4 @ X3 @ X2 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X7 @ X6 @ X5 @ X4 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X7 ) @ ( k2_xboole_0 @ ( k2_tarski @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(l75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X10 @ X11 @ X12 @ X13 ) @ ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l75_enumset1])).

thf('34',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X20 @ X21 @ X22 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k2_tarski @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X7 @ X6 @ X5 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      = ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','37'])).

thf('39',plain,(
    ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H )
 != ( k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(demod,[status(thm)],['0','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UsJDLz6sGH
% 0.16/0.38  % Computer   : n014.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:52:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 107 iterations in 0.131s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.62  thf(sk_H_type, type, sk_H: $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.41/0.62  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.41/0.62  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.41/0.62                                           $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(sk_G_type, type, sk_G: $i).
% 0.41/0.62  thf(t66_enumset1, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.62     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.62       ( k2_xboole_0 @
% 0.41/0.62         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.62        ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.62          ( k2_xboole_0 @
% 0.41/0.62            ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t66_enumset1])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.41/0.62         != (k2_xboole_0 @ (k3_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.41/0.62             (k1_enumset1 @ sk_F @ sk_G @ sk_H)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t42_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.62  thf(t41_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k2_tarski @ A @ B ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((k2_tarski @ X18 @ X19)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((k2_tarski @ X18 @ X19)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X19)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.41/0.62  thf(t4_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( k2_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 0.41/0.62       ( k2_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k2_tarski @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['2', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0))
% 0.41/0.62           = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.41/0.62              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.41/0.62  thf(t44_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X1) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X2)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X4) @ 
% 0.41/0.62              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf(t47_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.41/0.62     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.41/0.62       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.62         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.41/0.62              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X4 @ X3) @ 
% 0.41/0.62              (k1_enumset1 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['16', '17'])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.41/0.62           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['13', '18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ X5)
% 0.41/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.41/0.62              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X5)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k3_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2) @ 
% 0.41/0.62           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_enumset1 @ X3 @ X2 @ X1) @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.41/0.62           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ 
% 0.41/0.62               (k2_tarski @ X1 @ X0))))),
% 0.41/0.62      inference('sup+', [status(thm)], ['1', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X4 @ X3 @ X2) @ (k2_tarski @ X1 @ X0))
% 0.41/0.62           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['13', '18'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.41/0.62           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.62              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.62         ((k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X27) @ 
% 0.41/0.62              (k2_enumset1 @ X28 @ X29 @ X30 @ X31)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_tarski @ X0) @ X3)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X6 @ X5 @ X4) @ 
% 0.41/0.62           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.41/0.62              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.62         ((k2_enumset1 @ X23 @ X24 @ X25 @ X26)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_enumset1 @ X24 @ X25 @ X26)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.41/0.62              (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_enumset1 @ X7 @ X6 @ X5 @ X4) @ 
% 0.41/0.62           (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X7) @ 
% 0.41/0.62              (k2_xboole_0 @ (k2_tarski @ X6 @ X5) @ 
% 0.41/0.62               (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))))),
% 0.41/0.62      inference('sup+', [status(thm)], ['28', '31'])).
% 0.41/0.62  thf(l75_enumset1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.41/0.62     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.41/0.62       ( k2_xboole_0 @
% 0.41/0.62         ( k2_enumset1 @ A @ B @ C @ D ) @ ( k2_enumset1 @ E @ F @ G @ H ) ) ))).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, 
% 0.41/0.62         X17 : $i]:
% 0.41/0.62         ((k6_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 @ X17)
% 0.41/0.62           = (k2_xboole_0 @ (k2_enumset1 @ X10 @ X11 @ X12 @ X13) @ 
% 0.41/0.62              (k2_enumset1 @ X14 @ X15 @ X16 @ X17)))),
% 0.41/0.62      inference('cnf', [status(esa)], [l75_enumset1])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((k1_enumset1 @ X20 @ X21 @ X22)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k2_tarski @ X21 @ X22)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k2_xboole_0 @ X2 @ X3) @ X4)
% 0.41/0.62           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_1])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X3)
% 0.41/0.62           = (k2_xboole_0 @ (k1_tarski @ X2) @ 
% 0.41/0.62              (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ X3)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.41/0.62           = (k2_xboole_0 @ (k1_enumset1 @ X7 @ X6 @ X5) @ 
% 0.41/0.62              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '33', '36'])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ (k3_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3) @ 
% 0.41/0.62           (k1_enumset1 @ X2 @ X1 @ X0))
% 0.41/0.62           = (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['25', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (((k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ sk_H)
% 0.41/0.62         != (k6_enumset1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F @ sk_G @ 
% 0.41/0.62             sk_H))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '38'])).
% 0.41/0.62  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
