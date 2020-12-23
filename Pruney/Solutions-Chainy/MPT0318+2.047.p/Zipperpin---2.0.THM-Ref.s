%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TEOOE71Gm6

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:27 EST 2020

% Result     : Theorem 6.91s
% Output     : Refutation 6.91s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 471 expanded)
%              Number of leaves         :   34 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          : 1209 (4534 expanded)
%              Number of equality atoms :  168 ( 675 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X48 @ X47 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t66_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 ) @ ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t66_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','19'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X1 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','25'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','39','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','49'])).

thf('51',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('52',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X45 @ X46 ) )
      = ( k2_xboole_0 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('63',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('66',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('70',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51 != X50 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X50 ) )
       != ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('71',plain,(
    ! [X50: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X50 ) )
     != ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('74',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','76'])).

thf('78',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['52','77'])).

thf('79',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X48 @ X47 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('81',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['26','39','48'])).

thf('86',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('88',plain,
    ( ( k1_xboole_0
      = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('90',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('92',plain,(
    ! [X50: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X50 ) )
     != ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('93',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
     != ( k1_tarski @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('95',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('96',plain,
    ( ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,
    ( ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','97'])).

thf('99',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['88','98'])).

thf('100',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['78','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TEOOE71Gm6
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.91/7.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.91/7.10  % Solved by: fo/fo7.sh
% 6.91/7.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.91/7.10  % done 7506 iterations in 6.648s
% 6.91/7.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.91/7.10  % SZS output start Refutation
% 6.91/7.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.91/7.10  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 6.91/7.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.91/7.10  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.91/7.10  thf(sk_A_type, type, sk_A: $i).
% 6.91/7.10  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 6.91/7.10  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 6.91/7.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.91/7.10  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 6.91/7.10  thf(sk_B_type, type, sk_B: $i).
% 6.91/7.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.91/7.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 6.91/7.10  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 6.91/7.10                                           $i > $i).
% 6.91/7.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.91/7.10  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 6.91/7.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.91/7.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.91/7.10  thf(t130_zfmisc_1, conjecture,
% 6.91/7.10    (![A:$i,B:$i]:
% 6.91/7.10     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 6.91/7.10       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 6.91/7.10         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 6.91/7.10  thf(zf_stmt_0, negated_conjecture,
% 6.91/7.10    (~( ![A:$i,B:$i]:
% 6.91/7.10        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 6.91/7.10          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 6.91/7.10            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 6.91/7.10    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 6.91/7.10  thf('0', plain,
% 6.91/7.10      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 6.91/7.10        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 6.91/7.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.91/7.10  thf('1', plain,
% 6.91/7.10      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('split', [status(esa)], ['0'])).
% 6.91/7.10  thf(t113_zfmisc_1, axiom,
% 6.91/7.10    (![A:$i,B:$i]:
% 6.91/7.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.91/7.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.91/7.10  thf('2', plain,
% 6.91/7.10      (![X47 : $i, X48 : $i]:
% 6.91/7.10         (((X47) = (k1_xboole_0))
% 6.91/7.10          | ((X48) = (k1_xboole_0))
% 6.91/7.10          | ((k2_zfmisc_1 @ X48 @ X47) != (k1_xboole_0)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.91/7.10  thf('3', plain,
% 6.91/7.10      (((((k1_xboole_0) != (k1_xboole_0))
% 6.91/7.10         | ((sk_A) = (k1_xboole_0))
% 6.91/7.10         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('sup-', [status(thm)], ['1', '2'])).
% 6.91/7.10  thf('4', plain,
% 6.91/7.10      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('simplify', [status(thm)], ['3'])).
% 6.91/7.10  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 6.91/7.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.91/7.10  thf('6', plain,
% 6.91/7.10      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 6.91/7.10  thf(t70_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 6.91/7.10  thf('7', plain,
% 6.91/7.10      (![X18 : $i, X19 : $i]:
% 6.91/7.10         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 6.91/7.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.91/7.10  thf(t69_enumset1, axiom,
% 6.91/7.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 6.91/7.10  thf('8', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 6.91/7.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.91/7.10  thf('9', plain,
% 6.91/7.10      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['7', '8'])).
% 6.91/7.10  thf(t71_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i]:
% 6.91/7.10     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 6.91/7.10  thf('10', plain,
% 6.91/7.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.91/7.10         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 6.91/7.10           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 6.91/7.10      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.91/7.10  thf('11', plain,
% 6.91/7.10      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['9', '10'])).
% 6.91/7.10  thf('12', plain,
% 6.91/7.10      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['9', '10'])).
% 6.91/7.10  thf(t75_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 6.91/7.10     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 6.91/7.10       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 6.91/7.10  thf('13', plain,
% 6.91/7.10      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.91/7.10         ((k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 6.91/7.10           = (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 6.91/7.10      inference('cnf', [status(esa)], [t75_enumset1])).
% 6.91/7.10  thf('14', plain,
% 6.91/7.10      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['7', '8'])).
% 6.91/7.10  thf(t66_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 6.91/7.10     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 6.91/7.10       ( k2_xboole_0 @
% 6.91/7.10         ( k3_enumset1 @ A @ B @ C @ D @ E ) @ ( k1_enumset1 @ F @ G @ H ) ) ))).
% 6.91/7.10  thf('15', plain,
% 6.91/7.10      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 6.91/7.10         X16 : $i]:
% 6.91/7.10         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 6.91/7.10           = (k2_xboole_0 @ (k3_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13) @ 
% 6.91/7.10              (k1_enumset1 @ X14 @ X15 @ X16)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t66_enumset1])).
% 6.91/7.10  thf('16', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 6.91/7.10         ((k6_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 6.91/7.10           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 6.91/7.10              (k1_tarski @ X0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['14', '15'])).
% 6.91/7.10  thf('17', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.91/7.10         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 6.91/7.10           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 6.91/7.10              (k1_tarski @ X0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['13', '16'])).
% 6.91/7.10  thf(t72_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i,D:$i]:
% 6.91/7.10     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 6.91/7.10  thf('18', plain,
% 6.91/7.10      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.91/7.10         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 6.91/7.10           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 6.91/7.10      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.91/7.10  thf('19', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.91/7.10         ((k5_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X0 @ X0)
% 6.91/7.10           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 6.91/7.10              (k1_tarski @ X0)))),
% 6.91/7.10      inference('demod', [status(thm)], ['17', '18'])).
% 6.91/7.10  thf('20', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 @ X1 @ X1)
% 6.91/7.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['12', '19'])).
% 6.91/7.10  thf(t74_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.91/7.10     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 6.91/7.10       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 6.91/7.10  thf('21', plain,
% 6.91/7.10      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 6.91/7.10         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 6.91/7.10           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 6.91/7.10      inference('cnf', [status(esa)], [t74_enumset1])).
% 6.91/7.10  thf(t73_enumset1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 6.91/7.10     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 6.91/7.10       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 6.91/7.10  thf('22', plain,
% 6.91/7.10      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 6.91/7.10         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 6.91/7.10           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 6.91/7.10      inference('cnf', [status(esa)], [t73_enumset1])).
% 6.91/7.10  thf('23', plain,
% 6.91/7.10      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 6.91/7.10         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 6.91/7.10           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 6.91/7.10      inference('cnf', [status(esa)], [t72_enumset1])).
% 6.91/7.10  thf('24', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.91/7.10         ((k4_enumset1 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 6.91/7.10           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['22', '23'])).
% 6.91/7.10  thf('25', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k2_enumset1 @ X0 @ X1 @ X1 @ X1)
% 6.91/7.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 6.91/7.10      inference('demod', [status(thm)], ['20', '21', '24'])).
% 6.91/7.10  thf('26', plain,
% 6.91/7.10      (![X0 : $i]:
% 6.91/7.10         ((k1_tarski @ X0)
% 6.91/7.10           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['11', '25'])).
% 6.91/7.10  thf(t92_xboole_1, axiom,
% 6.91/7.10    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 6.91/7.10  thf('27', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 6.91/7.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.91/7.10  thf(t91_xboole_1, axiom,
% 6.91/7.10    (![A:$i,B:$i,C:$i]:
% 6.91/7.10     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.91/7.10       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 6.91/7.10  thf('28', plain,
% 6.91/7.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 6.91/7.10           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.91/7.10  thf('29', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 6.91/7.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['27', '28'])).
% 6.91/7.10  thf('30', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 6.91/7.10           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['27', '28'])).
% 6.91/7.10  thf('31', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 6.91/7.10      inference('cnf', [status(esa)], [t92_xboole_1])).
% 6.91/7.10  thf(t5_boole, axiom,
% 6.91/7.10    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.91/7.10  thf('32', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 6.91/7.10      inference('cnf', [status(esa)], [t5_boole])).
% 6.91/7.10  thf('33', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 6.91/7.10      inference('sup+', [status(thm)], ['31', '32'])).
% 6.91/7.10  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['30', '33'])).
% 6.91/7.10  thf('35', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 6.91/7.10      inference('demod', [status(thm)], ['29', '34'])).
% 6.91/7.10  thf(t95_xboole_1, axiom,
% 6.91/7.10    (![A:$i,B:$i]:
% 6.91/7.10     ( ( k3_xboole_0 @ A @ B ) =
% 6.91/7.10       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 6.91/7.10  thf('36', plain,
% 6.91/7.10      (![X7 : $i, X8 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X7 @ X8)
% 6.91/7.10           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t95_xboole_1])).
% 6.91/7.10  thf('37', plain,
% 6.91/7.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 6.91/7.10           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.91/7.10  thf('38', plain,
% 6.91/7.10      (![X7 : $i, X8 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X7 @ X8)
% 6.91/7.10           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 6.91/7.10      inference('demod', [status(thm)], ['36', '37'])).
% 6.91/7.10  thf('39', plain,
% 6.91/7.10      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['35', '38'])).
% 6.91/7.10  thf('40', plain,
% 6.91/7.10      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['9', '10'])).
% 6.91/7.10  thf('41', plain,
% 6.91/7.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 6.91/7.10         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 6.91/7.10           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 6.91/7.10      inference('cnf', [status(esa)], [t71_enumset1])).
% 6.91/7.10  thf('42', plain,
% 6.91/7.10      (![X18 : $i, X19 : $i]:
% 6.91/7.10         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 6.91/7.10      inference('cnf', [status(esa)], [t70_enumset1])).
% 6.91/7.10  thf(l51_zfmisc_1, axiom,
% 6.91/7.10    (![A:$i,B:$i]:
% 6.91/7.10     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 6.91/7.10  thf('43', plain,
% 6.91/7.10      (![X45 : $i, X46 : $i]:
% 6.91/7.10         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 6.91/7.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 6.91/7.10  thf('44', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['42', '43'])).
% 6.91/7.10  thf('45', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 6.91/7.10           = (k2_xboole_0 @ X1 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['41', '44'])).
% 6.91/7.10  thf('46', plain,
% 6.91/7.10      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['40', '45'])).
% 6.91/7.10  thf('47', plain,
% 6.91/7.10      (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['35', '38'])).
% 6.91/7.10  thf('48', plain,
% 6.91/7.10      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 6.91/7.10      inference('demod', [status(thm)], ['46', '47'])).
% 6.91/7.10  thf('49', plain,
% 6.91/7.10      (![X0 : $i]:
% 6.91/7.10         ((k1_tarski @ X0) = (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))),
% 6.91/7.10      inference('demod', [status(thm)], ['26', '39', '48'])).
% 6.91/7.10  thf('50', plain,
% 6.91/7.10      ((((k1_tarski @ sk_B) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('sup+', [status(thm)], ['6', '49'])).
% 6.91/7.10  thf('51', plain,
% 6.91/7.10      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 6.91/7.10  thf('52', plain,
% 6.91/7.10      ((((k1_xboole_0) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 6.91/7.10         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.10      inference('demod', [status(thm)], ['50', '51'])).
% 6.91/7.10  thf('53', plain,
% 6.91/7.10      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 6.91/7.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 6.91/7.10  thf('54', plain,
% 6.91/7.10      (![X45 : $i, X46 : $i]:
% 6.91/7.10         ((k3_tarski @ (k2_tarski @ X45 @ X46)) = (k2_xboole_0 @ X45 @ X46))),
% 6.91/7.10      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 6.91/7.10  thf('55', plain,
% 6.91/7.10      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['53', '54'])).
% 6.91/7.10  thf('56', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 6.91/7.10      inference('cnf', [status(esa)], [t5_boole])).
% 6.91/7.10  thf('57', plain,
% 6.91/7.10      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 6.91/7.10           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 6.91/7.10      inference('cnf', [status(esa)], [t91_xboole_1])).
% 6.91/7.10  thf('58', plain,
% 6.91/7.10      (![X0 : $i, X1 : $i]:
% 6.91/7.10         ((k5_xboole_0 @ X0 @ X1)
% 6.91/7.10           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['56', '57'])).
% 6.91/7.10  thf('59', plain,
% 6.91/7.10      (![X7 : $i, X8 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X7 @ X8)
% 6.91/7.10           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 6.91/7.10      inference('demod', [status(thm)], ['36', '37'])).
% 6.91/7.10  thf('60', plain,
% 6.91/7.10      (![X0 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 6.91/7.10           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['58', '59'])).
% 6.91/7.10  thf('61', plain,
% 6.91/7.10      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.10         = (k5_xboole_0 @ k1_xboole_0 @ (k3_tarski @ (k1_tarski @ k1_xboole_0))))),
% 6.91/7.10      inference('sup+', [status(thm)], ['55', '60'])).
% 6.91/7.10  thf('62', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.91/7.10      inference('sup+', [status(thm)], ['30', '33'])).
% 6.91/7.10  thf('63', plain,
% 6.91/7.10      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.10         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 6.91/7.10      inference('demod', [status(thm)], ['61', '62'])).
% 6.91/7.10  thf('64', plain,
% 6.91/7.10      (![X0 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 6.91/7.10           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.91/7.10      inference('sup+', [status(thm)], ['58', '59'])).
% 6.91/7.10  thf('65', plain,
% 6.91/7.10      (![X7 : $i, X8 : $i]:
% 6.91/7.10         ((k3_xboole_0 @ X7 @ X8)
% 6.91/7.10           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 6.91/7.10      inference('demod', [status(thm)], ['36', '37'])).
% 6.91/7.10  thf('66', plain,
% 6.91/7.10      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.11         = (k5_xboole_0 @ k1_xboole_0 @ 
% 6.91/7.11            (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)))),
% 6.91/7.11      inference('sup+', [status(thm)], ['64', '65'])).
% 6.91/7.11  thf(t100_xboole_1, axiom,
% 6.91/7.11    (![A:$i,B:$i]:
% 6.91/7.11     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.91/7.11  thf('67', plain,
% 6.91/7.11      (![X0 : $i, X1 : $i]:
% 6.91/7.11         ((k4_xboole_0 @ X0 @ X1)
% 6.91/7.11           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.91/7.11      inference('cnf', [status(esa)], [t100_xboole_1])).
% 6.91/7.11  thf('68', plain,
% 6.91/7.11      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.11         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 6.91/7.11      inference('demod', [status(thm)], ['66', '67'])).
% 6.91/7.11  thf('69', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 6.91/7.11  thf(t20_zfmisc_1, axiom,
% 6.91/7.11    (![A:$i,B:$i]:
% 6.91/7.11     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 6.91/7.11         ( k1_tarski @ A ) ) <=>
% 6.91/7.11       ( ( A ) != ( B ) ) ))).
% 6.91/7.11  thf('70', plain,
% 6.91/7.11      (![X50 : $i, X51 : $i]:
% 6.91/7.11         (((X51) != (X50))
% 6.91/7.11          | ((k4_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X50))
% 6.91/7.11              != (k1_tarski @ X51)))),
% 6.91/7.11      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 6.91/7.11  thf('71', plain,
% 6.91/7.11      (![X50 : $i]:
% 6.91/7.11         ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X50))
% 6.91/7.11           != (k1_tarski @ X50))),
% 6.91/7.11      inference('simplify', [status(thm)], ['70'])).
% 6.91/7.11  thf('72', plain,
% 6.91/7.11      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['69', '71'])).
% 6.91/7.11  thf('73', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 6.91/7.11  thf('74', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 6.91/7.11  thf('75', plain,
% 6.91/7.11      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('demod', [status(thm)], ['72', '73', '74'])).
% 6.91/7.11  thf('76', plain,
% 6.91/7.11      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['68', '75'])).
% 6.91/7.11  thf('77', plain,
% 6.91/7.11      ((((k3_tarski @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['63', '76'])).
% 6.91/7.11  thf('78', plain,
% 6.91/7.11      (($false)
% 6.91/7.11         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['52', '77'])).
% 6.91/7.11  thf('79', plain,
% 6.91/7.11      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('split', [status(esa)], ['0'])).
% 6.91/7.11  thf('80', plain,
% 6.91/7.11      (![X47 : $i, X48 : $i]:
% 6.91/7.11         (((X47) = (k1_xboole_0))
% 6.91/7.11          | ((X48) = (k1_xboole_0))
% 6.91/7.11          | ((k2_zfmisc_1 @ X48 @ X47) != (k1_xboole_0)))),
% 6.91/7.11      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.91/7.11  thf('81', plain,
% 6.91/7.11      (((((k1_xboole_0) != (k1_xboole_0))
% 6.91/7.11         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 6.91/7.11         | ((sk_A) = (k1_xboole_0))))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['79', '80'])).
% 6.91/7.11  thf('82', plain,
% 6.91/7.11      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify', [status(thm)], ['81'])).
% 6.91/7.11  thf('83', plain, (((sk_A) != (k1_xboole_0))),
% 6.91/7.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.91/7.11  thf('84', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.91/7.11  thf('85', plain,
% 6.91/7.11      (![X0 : $i]:
% 6.91/7.11         ((k1_tarski @ X0) = (k3_tarski @ (k1_tarski @ (k1_tarski @ X0))))),
% 6.91/7.11      inference('demod', [status(thm)], ['26', '39', '48'])).
% 6.91/7.11  thf('86', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup+', [status(thm)], ['84', '85'])).
% 6.91/7.11  thf('87', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.91/7.11  thf('88', plain,
% 6.91/7.11      ((((k1_xboole_0) = (k3_tarski @ (k1_tarski @ k1_xboole_0))))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('demod', [status(thm)], ['86', '87'])).
% 6.91/7.11  thf('89', plain,
% 6.91/7.11      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.11         = (k3_tarski @ (k1_tarski @ k1_xboole_0)))),
% 6.91/7.11      inference('demod', [status(thm)], ['61', '62'])).
% 6.91/7.11  thf('90', plain,
% 6.91/7.11      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 6.91/7.11         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 6.91/7.11      inference('demod', [status(thm)], ['66', '67'])).
% 6.91/7.11  thf('91', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.91/7.11  thf('92', plain,
% 6.91/7.11      (![X50 : $i]:
% 6.91/7.11         ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X50))
% 6.91/7.11           != (k1_tarski @ X50))),
% 6.91/7.11      inference('simplify', [status(thm)], ['70'])).
% 6.91/7.11  thf('93', plain,
% 6.91/7.11      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0) != (k1_tarski @ sk_B)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['91', '92'])).
% 6.91/7.11  thf('94', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.91/7.11  thf('95', plain,
% 6.91/7.11      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.91/7.11  thf('96', plain,
% 6.91/7.11      ((((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('demod', [status(thm)], ['93', '94', '95'])).
% 6.91/7.11  thf('97', plain,
% 6.91/7.11      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['90', '96'])).
% 6.91/7.11  thf('98', plain,
% 6.91/7.11      ((((k3_tarski @ (k1_tarski @ k1_xboole_0)) != (k1_xboole_0)))
% 6.91/7.11         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 6.91/7.11      inference('sup-', [status(thm)], ['89', '97'])).
% 6.91/7.11  thf('99', plain,
% 6.91/7.11      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 6.91/7.11      inference('simplify_reflect-', [status(thm)], ['88', '98'])).
% 6.91/7.11  thf('100', plain,
% 6.91/7.11      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 6.91/7.11       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 6.91/7.11      inference('split', [status(esa)], ['0'])).
% 6.91/7.11  thf('101', plain,
% 6.91/7.11      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 6.91/7.11      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 6.91/7.11  thf('102', plain, ($false),
% 6.91/7.11      inference('simpl_trail', [status(thm)], ['78', '101'])).
% 6.91/7.11  
% 6.91/7.11  % SZS output end Refutation
% 6.91/7.11  
% 6.91/7.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
