%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l0IIKAShyE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:32 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 113 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  887 (1623 expanded)
%              Number of equality atoms :   65 ( 119 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('23',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ X41 @ ( k2_xboole_0 @ X38 @ X40 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X41 @ X38 ) @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(t132_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) )
        & ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_zfmisc_1])).

thf('24',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X38 @ X40 ) @ X39 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) )
    | ( ( k2_zfmisc_1 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['24'])).

thf('40',plain,(
    ( k2_zfmisc_1 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['30','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l0IIKAShyE
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:03:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 1.22/1.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.22/1.40  % Solved by: fo/fo7.sh
% 1.22/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.40  % done 305 iterations in 0.952s
% 1.22/1.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.22/1.40  % SZS output start Refutation
% 1.22/1.40  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 1.22/1.40                                           $i > $i).
% 1.22/1.40  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.22/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.40  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 1.22/1.40  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.22/1.40  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 1.22/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.22/1.40  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 1.22/1.40  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.22/1.40  thf(sk_C_type, type, sk_C: $i).
% 1.22/1.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.22/1.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.22/1.40  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.22/1.40  thf(t70_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.22/1.40  thf('0', plain,
% 1.22/1.40      (![X9 : $i, X10 : $i]:
% 1.22/1.40         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 1.22/1.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.22/1.40  thf(t69_enumset1, axiom,
% 1.22/1.40    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.22/1.40  thf('1', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 1.22/1.40      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.40  thf('2', plain,
% 1.22/1.40      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.22/1.40      inference('sup+', [status(thm)], ['0', '1'])).
% 1.22/1.40  thf(t71_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i]:
% 1.22/1.40     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.22/1.40  thf('3', plain,
% 1.22/1.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.22/1.40         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 1.22/1.40           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 1.22/1.40      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.22/1.40  thf(t72_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.40     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 1.22/1.40  thf('4', plain,
% 1.22/1.40      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.40         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 1.22/1.40           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 1.22/1.40      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.22/1.40  thf(t74_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.22/1.40     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 1.22/1.40       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 1.22/1.40  thf('5', plain,
% 1.22/1.40      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.22/1.40         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.22/1.40           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 1.22/1.40      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.22/1.40  thf(t68_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 1.22/1.40     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 1.22/1.40       ( k2_xboole_0 @
% 1.22/1.40         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 1.22/1.40  thf('6', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.22/1.40         ((k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 1.22/1.40           = (k2_xboole_0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6) @ 
% 1.22/1.40              (k1_tarski @ X7)))),
% 1.22/1.40      inference('cnf', [status(esa)], [t68_enumset1])).
% 1.22/1.40  thf('7', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.22/1.40         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 1.22/1.40           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 1.22/1.40              (k1_tarski @ X6)))),
% 1.22/1.40      inference('sup+', [status(thm)], ['5', '6'])).
% 1.22/1.40  thf(t75_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.22/1.40     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 1.22/1.40       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 1.22/1.40  thf('8', plain,
% 1.22/1.40      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.22/1.40         ((k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 1.22/1.40           = (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 1.22/1.40      inference('cnf', [status(esa)], [t75_enumset1])).
% 1.22/1.40  thf('9', plain,
% 1.22/1.40      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.22/1.40         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 1.22/1.40           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 1.22/1.40      inference('cnf', [status(esa)], [t74_enumset1])).
% 1.22/1.40  thf('10', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.22/1.40         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 1.22/1.40           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.40      inference('sup+', [status(thm)], ['8', '9'])).
% 1.22/1.40  thf('11', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.22/1.40           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.40      inference('sup+', [status(thm)], ['7', '10'])).
% 1.22/1.40  thf(t73_enumset1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.22/1.40     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 1.22/1.40       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 1.22/1.40  thf('12', plain,
% 1.22/1.40      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.22/1.40         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.22/1.40           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 1.22/1.40      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.22/1.40  thf('13', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 1.22/1.40           (k1_tarski @ X0)) = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 1.22/1.40      inference('demod', [status(thm)], ['11', '12'])).
% 1.22/1.40  thf('14', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 1.22/1.40           = (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 1.22/1.40      inference('sup+', [status(thm)], ['4', '13'])).
% 1.22/1.40  thf('15', plain,
% 1.22/1.40      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.22/1.40         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 1.22/1.40           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 1.22/1.40      inference('cnf', [status(esa)], [t73_enumset1])).
% 1.22/1.40  thf('16', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 1.22/1.40           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 1.22/1.40      inference('demod', [status(thm)], ['14', '15'])).
% 1.22/1.40  thf('17', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 1.22/1.40           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 1.22/1.40      inference('sup+', [status(thm)], ['3', '16'])).
% 1.22/1.40  thf('18', plain,
% 1.22/1.40      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.22/1.40         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 1.22/1.40           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 1.22/1.40      inference('cnf', [status(esa)], [t72_enumset1])).
% 1.22/1.40  thf('19', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 1.22/1.40           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 1.22/1.40      inference('demod', [status(thm)], ['17', '18'])).
% 1.22/1.40  thf('20', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.22/1.40           = (k2_enumset1 @ X0 @ X0 @ X0 @ X1))),
% 1.22/1.40      inference('sup+', [status(thm)], ['2', '19'])).
% 1.22/1.40  thf('21', plain,
% 1.22/1.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.22/1.40         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 1.22/1.40           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 1.22/1.40      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.22/1.40  thf('22', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.22/1.40           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.22/1.40      inference('demod', [status(thm)], ['20', '21'])).
% 1.22/1.40  thf(t120_zfmisc_1, axiom,
% 1.22/1.40    (![A:$i,B:$i,C:$i]:
% 1.22/1.40     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 1.22/1.40         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.22/1.40       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 1.22/1.40         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 1.22/1.40  thf('23', plain,
% 1.22/1.40      (![X38 : $i, X40 : $i, X41 : $i]:
% 1.22/1.40         ((k2_zfmisc_1 @ X41 @ (k2_xboole_0 @ X38 @ X40))
% 1.22/1.40           = (k2_xboole_0 @ (k2_zfmisc_1 @ X41 @ X38) @ 
% 1.22/1.40              (k2_zfmisc_1 @ X41 @ X40)))),
% 1.22/1.40      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.22/1.40  thf(t132_zfmisc_1, conjecture,
% 1.22/1.40    (![A:$i,B:$i,C:$i]:
% 1.22/1.40     ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 1.22/1.40         ( k2_xboole_0 @
% 1.22/1.40           ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 1.22/1.40           ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 1.22/1.40       ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 1.22/1.40         ( k2_xboole_0 @
% 1.22/1.40           ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 1.22/1.40           ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ))).
% 1.22/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.40    (~( ![A:$i,B:$i,C:$i]:
% 1.22/1.40        ( ( ( k2_zfmisc_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 1.22/1.40            ( k2_xboole_0 @
% 1.22/1.40              ( k2_zfmisc_1 @ C @ ( k1_tarski @ A ) ) @ 
% 1.22/1.40              ( k2_zfmisc_1 @ C @ ( k1_tarski @ B ) ) ) ) & 
% 1.22/1.40          ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ C ) =
% 1.22/1.40            ( k2_xboole_0 @
% 1.22/1.40              ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ C ) @ 
% 1.22/1.40              ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) ) ) )),
% 1.22/1.40    inference('cnf.neg', [status(esa)], [t132_zfmisc_1])).
% 1.22/1.40  thf('24', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))
% 1.22/1.40        | ((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40            != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40                (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 1.22/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.40  thf('25', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          != (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40              (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 1.22/1.40      inference('split', [status(esa)], ['24'])).
% 1.22/1.40  thf('26', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          != (k2_zfmisc_1 @ sk_C @ 
% 1.22/1.40              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 1.22/1.40      inference('sup-', [status(thm)], ['23', '25'])).
% 1.22/1.40  thf('27', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          != (k2_zfmisc_1 @ sk_C @ (k1_enumset1 @ sk_A @ sk_A @ sk_B))))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 1.22/1.40      inference('sup-', [status(thm)], ['22', '26'])).
% 1.22/1.40  thf('28', plain,
% 1.22/1.40      (![X9 : $i, X10 : $i]:
% 1.22/1.40         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 1.22/1.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.22/1.40  thf('29', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          != (k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 1.22/1.40      inference('demod', [status(thm)], ['27', '28'])).
% 1.22/1.40  thf('30', plain,
% 1.22/1.40      (($false)
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))))),
% 1.22/1.40      inference('simplify', [status(thm)], ['29'])).
% 1.22/1.40  thf('31', plain,
% 1.22/1.40      (![X0 : $i, X1 : $i]:
% 1.22/1.40         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 1.22/1.40           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 1.22/1.40      inference('demod', [status(thm)], ['20', '21'])).
% 1.22/1.40  thf('32', plain,
% 1.22/1.40      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.22/1.40         ((k2_zfmisc_1 @ (k2_xboole_0 @ X38 @ X40) @ X39)
% 1.22/1.40           = (k2_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 1.22/1.40              (k2_zfmisc_1 @ X40 @ X39)))),
% 1.22/1.40      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 1.22/1.40  thf('33', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          != (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40              (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 1.22/1.40      inference('split', [status(esa)], ['24'])).
% 1.22/1.40  thf('34', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          != (k2_zfmisc_1 @ 
% 1.22/1.40              (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ sk_C)))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 1.22/1.40      inference('sup-', [status(thm)], ['32', '33'])).
% 1.22/1.40  thf('35', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          != (k2_zfmisc_1 @ (k1_enumset1 @ sk_A @ sk_A @ sk_B) @ sk_C)))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 1.22/1.40      inference('sup-', [status(thm)], ['31', '34'])).
% 1.22/1.40  thf('36', plain,
% 1.22/1.40      (![X9 : $i, X10 : $i]:
% 1.22/1.40         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 1.22/1.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.22/1.40  thf('37', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          != (k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 1.22/1.40         <= (~
% 1.22/1.40             (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40                = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40                   (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C)))))),
% 1.22/1.40      inference('demod', [status(thm)], ['35', '36'])).
% 1.22/1.40  thf('38', plain,
% 1.22/1.40      ((((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 1.22/1.40      inference('simplify', [status(thm)], ['37'])).
% 1.22/1.40  thf('39', plain,
% 1.22/1.40      (~
% 1.22/1.40       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B))))) | 
% 1.22/1.40       ~
% 1.22/1.40       (((k2_zfmisc_1 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.22/1.40          = (k2_xboole_0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_C) @ 
% 1.22/1.40             (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C))))),
% 1.22/1.40      inference('split', [status(esa)], ['24'])).
% 1.22/1.40  thf('40', plain,
% 1.22/1.40      (~
% 1.22/1.40       (((k2_zfmisc_1 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.22/1.40          = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_A)) @ 
% 1.22/1.40             (k2_zfmisc_1 @ sk_C @ (k1_tarski @ sk_B)))))),
% 1.22/1.40      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 1.22/1.40  thf('41', plain, ($false),
% 1.22/1.40      inference('simpl_trail', [status(thm)], ['30', '40'])).
% 1.22/1.40  
% 1.22/1.40  % SZS output end Refutation
% 1.22/1.40  
% 1.22/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
