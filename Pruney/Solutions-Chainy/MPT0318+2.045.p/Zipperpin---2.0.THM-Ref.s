%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywEUm7Efkl

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:27 EST 2020

% Result     : Theorem 18.53s
% Output     : Refutation 18.53s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 180 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  897 (1934 expanded)
%              Number of equality atoms :  107 ( 215 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('9',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X51 != X50 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X51 ) @ ( k1_tarski @ X50 ) )
       != ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('10',plain,(
    ! [X50: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X50 ) )
     != ( k1_tarski @ X50 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_enumset1 @ X20 @ X20 @ X21 @ X22 )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_enumset1 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('15',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t62_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 )
      = ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ ( k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t62_enumset1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k5_xboole_0 @ X8 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k5_xboole_0 @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X7 ) @ ( k3_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X7 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_xboole_0 @ ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ X4 ) @ ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('39',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 )
      = ( k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31 )
      = ( k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X4 ) @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['12','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','46'])).

thf('48',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X48 @ X47 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['12','45'])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['48','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ywEUm7Efkl
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:02:00 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 18.53/18.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.53/18.78  % Solved by: fo/fo7.sh
% 18.53/18.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.53/18.78  % done 9482 iterations in 18.338s
% 18.53/18.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.53/18.78  % SZS output start Refutation
% 18.53/18.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 18.53/18.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 18.53/18.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 18.53/18.78  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 18.53/18.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.53/18.78  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 18.53/18.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 18.53/18.78  thf(sk_A_type, type, sk_A: $i).
% 18.53/18.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 18.53/18.78  thf(sk_B_type, type, sk_B: $i).
% 18.53/18.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.53/18.78  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 18.53/18.78                                           $i > $i).
% 18.53/18.78  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 18.53/18.78  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 18.53/18.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 18.53/18.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.53/18.78  thf(t130_zfmisc_1, conjecture,
% 18.53/18.78    (![A:$i,B:$i]:
% 18.53/18.78     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 18.53/18.78       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 18.53/18.78         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 18.53/18.78  thf(zf_stmt_0, negated_conjecture,
% 18.53/18.78    (~( ![A:$i,B:$i]:
% 18.53/18.78        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 18.53/18.78          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 18.53/18.78            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 18.53/18.78    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 18.53/18.78  thf('0', plain,
% 18.53/18.78      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 18.53/18.78        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 18.53/18.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.78  thf('1', plain,
% 18.53/18.78      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('split', [status(esa)], ['0'])).
% 18.53/18.78  thf(t113_zfmisc_1, axiom,
% 18.53/18.78    (![A:$i,B:$i]:
% 18.53/18.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 18.53/18.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 18.53/18.78  thf('2', plain,
% 18.53/18.78      (![X47 : $i, X48 : $i]:
% 18.53/18.78         (((X47) = (k1_xboole_0))
% 18.53/18.78          | ((X48) = (k1_xboole_0))
% 18.53/18.78          | ((k2_zfmisc_1 @ X48 @ X47) != (k1_xboole_0)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 18.53/18.78  thf('3', plain,
% 18.53/18.78      (((((k1_xboole_0) != (k1_xboole_0))
% 18.53/18.78         | ((sk_A) = (k1_xboole_0))
% 18.53/18.78         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('sup-', [status(thm)], ['1', '2'])).
% 18.53/18.78  thf('4', plain,
% 18.53/18.78      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('simplify', [status(thm)], ['3'])).
% 18.53/18.78  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 18.53/18.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.78  thf('6', plain,
% 18.53/18.78      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 18.53/18.78  thf(t70_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 18.53/18.78  thf('7', plain,
% 18.53/18.78      (![X18 : $i, X19 : $i]:
% 18.53/18.78         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 18.53/18.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 18.53/18.78  thf(t69_enumset1, axiom,
% 18.53/18.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 18.53/18.78  thf('8', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 18.53/18.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 18.53/18.78  thf(t20_zfmisc_1, axiom,
% 18.53/18.78    (![A:$i,B:$i]:
% 18.53/18.78     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 18.53/18.78         ( k1_tarski @ A ) ) <=>
% 18.53/18.78       ( ( A ) != ( B ) ) ))).
% 18.53/18.78  thf('9', plain,
% 18.53/18.78      (![X50 : $i, X51 : $i]:
% 18.53/18.78         (((X51) != (X50))
% 18.53/18.78          | ((k4_xboole_0 @ (k1_tarski @ X51) @ (k1_tarski @ X50))
% 18.53/18.78              != (k1_tarski @ X51)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 18.53/18.78  thf('10', plain,
% 18.53/18.78      (![X50 : $i]:
% 18.53/18.78         ((k4_xboole_0 @ (k1_tarski @ X50) @ (k1_tarski @ X50))
% 18.53/18.78           != (k1_tarski @ X50))),
% 18.53/18.78      inference('simplify', [status(thm)], ['9'])).
% 18.53/18.78  thf('11', plain,
% 18.53/18.78      (![X0 : $i]:
% 18.53/18.78         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 18.53/18.78           != (k1_tarski @ X0))),
% 18.53/18.78      inference('sup-', [status(thm)], ['8', '10'])).
% 18.53/18.78  thf('12', plain,
% 18.53/18.78      (![X0 : $i]:
% 18.53/18.78         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_enumset1 @ X0 @ X0 @ X0))
% 18.53/18.78           != (k1_tarski @ X0))),
% 18.53/18.78      inference('sup-', [status(thm)], ['7', '11'])).
% 18.53/18.78  thf(t71_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i]:
% 18.53/18.78     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 18.53/18.78  thf('13', plain,
% 18.53/18.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 18.53/18.78         ((k2_enumset1 @ X20 @ X20 @ X21 @ X22)
% 18.53/18.78           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 18.53/18.78      inference('cnf', [status(esa)], [t71_enumset1])).
% 18.53/18.78  thf(t72_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i,D:$i]:
% 18.53/18.78     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 18.53/18.78  thf('14', plain,
% 18.53/18.78      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 18.53/18.78         ((k3_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26)
% 18.53/18.78           = (k2_enumset1 @ X23 @ X24 @ X25 @ X26))),
% 18.53/18.78      inference('cnf', [status(esa)], [t72_enumset1])).
% 18.53/18.78  thf(t75_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 18.53/18.78     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 18.53/18.78       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 18.53/18.78  thf('15', plain,
% 18.53/18.78      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 18.53/18.78         ((k6_enumset1 @ X38 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44)
% 18.53/18.78           = (k5_enumset1 @ X38 @ X39 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 18.53/18.78      inference('cnf', [status(esa)], [t75_enumset1])).
% 18.53/18.78  thf(t74_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 18.53/18.78     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 18.53/18.78       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 18.53/18.78  thf('16', plain,
% 18.53/18.78      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 18.53/18.78         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 18.53/18.78           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 18.53/18.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 18.53/18.78  thf('17', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 18.53/18.78         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 18.53/18.78           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 18.53/18.78      inference('sup+', [status(thm)], ['15', '16'])).
% 18.53/18.78  thf(t73_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 18.53/18.78     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 18.53/18.78       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 18.53/18.78  thf('18', plain,
% 18.53/18.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 18.53/18.78         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 18.53/18.78           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 18.53/18.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 18.53/18.78  thf('19', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.53/18.78         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 18.53/18.78           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 18.53/18.78      inference('sup+', [status(thm)], ['17', '18'])).
% 18.53/18.78  thf(t62_enumset1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 18.53/18.78     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 18.53/18.78       ( k2_xboole_0 @
% 18.53/18.78         ( k1_tarski @ A ) @ ( k5_enumset1 @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 18.53/18.78  thf('20', plain,
% 18.53/18.78      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, 
% 18.53/18.78         X16 : $i]:
% 18.53/18.78         ((k6_enumset1 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)
% 18.53/18.78           = (k2_xboole_0 @ (k1_tarski @ X9) @ 
% 18.53/18.78              (k5_enumset1 @ X10 @ X11 @ X12 @ X13 @ X14 @ X15 @ X16)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t62_enumset1])).
% 18.53/18.78  thf(t95_xboole_1, axiom,
% 18.53/18.78    (![A:$i,B:$i]:
% 18.53/18.78     ( ( k3_xboole_0 @ A @ B ) =
% 18.53/18.78       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 18.53/18.78  thf('21', plain,
% 18.53/18.78      (![X7 : $i, X8 : $i]:
% 18.53/18.78         ((k3_xboole_0 @ X7 @ X8)
% 18.53/18.78           = (k5_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ (k2_xboole_0 @ X7 @ X8)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t95_xboole_1])).
% 18.53/18.78  thf(t91_xboole_1, axiom,
% 18.53/18.78    (![A:$i,B:$i,C:$i]:
% 18.53/18.78     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 18.53/18.78       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 18.53/18.78  thf('22', plain,
% 18.53/18.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 18.53/18.78           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.53/18.78  thf('23', plain,
% 18.53/18.78      (![X7 : $i, X8 : $i]:
% 18.53/18.78         ((k3_xboole_0 @ X7 @ X8)
% 18.53/18.78           = (k5_xboole_0 @ X7 @ (k5_xboole_0 @ X8 @ (k2_xboole_0 @ X7 @ X8))))),
% 18.53/18.78      inference('demod', [status(thm)], ['21', '22'])).
% 18.53/18.78  thf('24', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 18.53/18.78         ((k3_xboole_0 @ (k1_tarski @ X7) @ 
% 18.53/18.78           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 18.53/18.78           = (k5_xboole_0 @ (k1_tarski @ X7) @ 
% 18.53/18.78              (k5_xboole_0 @ 
% 18.53/18.78               (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 18.53/18.78               (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))))),
% 18.53/18.78      inference('sup+', [status(thm)], ['20', '23'])).
% 18.53/18.78  thf(t92_xboole_1, axiom,
% 18.53/18.78    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 18.53/18.78  thf('25', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 18.53/18.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 18.53/18.78  thf('26', plain,
% 18.53/18.78      (![X3 : $i, X4 : $i, X5 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ (k5_xboole_0 @ X3 @ X4) @ X5)
% 18.53/18.78           = (k5_xboole_0 @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 18.53/18.78  thf('27', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 18.53/18.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.53/18.78      inference('sup+', [status(thm)], ['25', '26'])).
% 18.53/18.78  thf('28', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 18.53/18.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.53/18.78      inference('sup+', [status(thm)], ['25', '26'])).
% 18.53/18.78  thf('29', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 18.53/18.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 18.53/18.78  thf(t5_boole, axiom,
% 18.53/18.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 18.53/18.78  thf('30', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 18.53/18.78      inference('cnf', [status(esa)], [t5_boole])).
% 18.53/18.78  thf('31', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 18.53/18.78      inference('sup+', [status(thm)], ['29', '30'])).
% 18.53/18.78  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 18.53/18.78      inference('sup+', [status(thm)], ['28', '31'])).
% 18.53/18.78  thf('33', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i]:
% 18.53/18.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 18.53/18.78      inference('demod', [status(thm)], ['27', '32'])).
% 18.53/18.78  thf('34', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 18.53/18.78           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 18.53/18.78           = (k5_xboole_0 @ (k1_tarski @ X7) @ 
% 18.53/18.78              (k3_xboole_0 @ (k1_tarski @ X7) @ 
% 18.53/18.78               (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))))),
% 18.53/18.78      inference('sup+', [status(thm)], ['24', '33'])).
% 18.53/18.78  thf(t100_xboole_1, axiom,
% 18.53/18.78    (![A:$i,B:$i]:
% 18.53/18.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 18.53/18.78  thf('35', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i]:
% 18.53/18.78         ((k4_xboole_0 @ X0 @ X1)
% 18.53/18.78           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 18.53/18.78  thf('36', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 18.53/18.78           (k6_enumset1 @ X7 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 18.53/18.78           = (k4_xboole_0 @ (k1_tarski @ X7) @ 
% 18.53/18.78              (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 18.53/18.78      inference('demod', [status(thm)], ['34', '35'])).
% 18.53/18.78  thf('37', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.53/18.78         ((k5_xboole_0 @ (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 18.53/18.78           (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))
% 18.53/18.78           = (k4_xboole_0 @ (k1_tarski @ X4) @ 
% 18.53/18.78              (k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 18.53/18.78      inference('sup+', [status(thm)], ['19', '36'])).
% 18.53/18.78  thf('38', plain,
% 18.53/18.78      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 18.53/18.78         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 18.53/18.78           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 18.53/18.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 18.53/18.78  thf('39', plain,
% 18.53/18.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 18.53/18.78         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 18.53/18.78           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 18.53/18.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 18.53/18.78  thf('40', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ X6) = (k1_xboole_0))),
% 18.53/18.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 18.53/18.78  thf('41', plain,
% 18.53/18.78      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 18.53/18.78         ((k5_enumset1 @ X32 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37)
% 18.53/18.78           = (k4_enumset1 @ X32 @ X33 @ X34 @ X35 @ X36 @ X37))),
% 18.53/18.78      inference('cnf', [status(esa)], [t74_enumset1])).
% 18.53/18.78  thf('42', plain,
% 18.53/18.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 18.53/18.78         ((k4_enumset1 @ X27 @ X27 @ X28 @ X29 @ X30 @ X31)
% 18.53/18.78           = (k3_enumset1 @ X27 @ X28 @ X29 @ X30 @ X31))),
% 18.53/18.78      inference('cnf', [status(esa)], [t73_enumset1])).
% 18.53/18.78  thf('43', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 18.53/18.78         ((k1_xboole_0)
% 18.53/18.78           = (k4_xboole_0 @ (k1_tarski @ X4) @ 
% 18.53/18.78              (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)))),
% 18.53/18.78      inference('demod', [status(thm)], ['37', '38', '39', '40', '41', '42'])).
% 18.53/18.78  thf('44', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 18.53/18.78         ((k1_xboole_0)
% 18.53/18.78           = (k4_xboole_0 @ (k1_tarski @ X3) @ 
% 18.53/18.78              (k2_enumset1 @ X3 @ X2 @ X1 @ X0)))),
% 18.53/18.78      inference('sup+', [status(thm)], ['14', '43'])).
% 18.53/18.78  thf('45', plain,
% 18.53/18.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.53/18.78         ((k1_xboole_0)
% 18.53/18.78           = (k4_xboole_0 @ (k1_tarski @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 18.53/18.78      inference('sup+', [status(thm)], ['13', '44'])).
% 18.53/18.78  thf('46', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 18.53/18.78      inference('demod', [status(thm)], ['12', '45'])).
% 18.53/18.78  thf('47', plain,
% 18.53/18.78      ((((k1_xboole_0) != (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('sup-', [status(thm)], ['6', '46'])).
% 18.53/18.78  thf('48', plain,
% 18.53/18.78      (($false)
% 18.53/18.78         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 18.53/18.78      inference('simplify', [status(thm)], ['47'])).
% 18.53/18.78  thf('49', plain,
% 18.53/18.78      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 18.53/18.78      inference('split', [status(esa)], ['0'])).
% 18.53/18.78  thf('50', plain,
% 18.53/18.78      (![X47 : $i, X48 : $i]:
% 18.53/18.78         (((X47) = (k1_xboole_0))
% 18.53/18.78          | ((X48) = (k1_xboole_0))
% 18.53/18.78          | ((k2_zfmisc_1 @ X48 @ X47) != (k1_xboole_0)))),
% 18.53/18.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 18.53/18.78  thf('51', plain,
% 18.53/18.78      (((((k1_xboole_0) != (k1_xboole_0))
% 18.53/18.78         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 18.53/18.78         | ((sk_A) = (k1_xboole_0))))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 18.53/18.78      inference('sup-', [status(thm)], ['49', '50'])).
% 18.53/18.78  thf('52', plain,
% 18.53/18.78      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 18.53/18.78      inference('simplify', [status(thm)], ['51'])).
% 18.53/18.78  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 18.53/18.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.53/18.78  thf('54', plain,
% 18.53/18.78      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 18.53/18.78      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 18.53/18.78  thf('55', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 18.53/18.78      inference('demod', [status(thm)], ['12', '45'])).
% 18.53/18.78  thf('56', plain,
% 18.53/18.78      ((((k1_xboole_0) != (k1_xboole_0)))
% 18.53/18.78         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 18.53/18.78      inference('sup-', [status(thm)], ['54', '55'])).
% 18.53/18.78  thf('57', plain,
% 18.53/18.78      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 18.53/18.78      inference('simplify', [status(thm)], ['56'])).
% 18.53/18.78  thf('58', plain,
% 18.53/18.78      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 18.53/18.78       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 18.53/18.78      inference('split', [status(esa)], ['0'])).
% 18.53/18.78  thf('59', plain,
% 18.53/18.78      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 18.53/18.78      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 18.53/18.78  thf('60', plain, ($false),
% 18.53/18.78      inference('simpl_trail', [status(thm)], ['48', '59'])).
% 18.53/18.78  
% 18.53/18.78  % SZS output end Refutation
% 18.53/18.78  
% 18.53/18.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
