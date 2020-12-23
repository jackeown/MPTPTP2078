%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ll0PCDkR5U

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:13 EST 2020

% Result     : Theorem 45.72s
% Output     : Refutation 45.78s
% Verified   : 
% Statistics : Number of formulae       :  311 (13074 expanded)
%              Number of leaves         :   35 (4391 expanded)
%              Depth                    :   41
%              Number of atoms          : 2948 (105525 expanded)
%              Number of equality atoms :  295 (13094 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('38',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('42',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('43',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('49',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('54',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('55',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 ) )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) @ ( k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('67',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('70',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('71',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','73'])).

thf('75',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('78',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('89',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('90',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('102',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('117',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['115','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('130',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['127','132','133','136','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','144'])).

thf('146',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','69','70','71','72'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('159',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('161',plain,
    ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('163',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('165',plain,
    ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['156','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('175',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) @ X1 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k5_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('181',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['155','182'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = ( k5_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k5_xboole_0 @ X2 @ ( k1_tarski @ sk_A ) ) )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['186','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('192',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('193',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['154','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('204',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 )
      = ( k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('205',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('208',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['206','209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['203','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['202','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['201','214'])).

thf('216',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('217',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['202','211'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('220',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['218','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('227',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['224','225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','85','86'])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['227','232'])).

thf('234',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['233','234','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('242',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k5_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['190','191','192'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_tarski @ X1 @ X1 ) ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','16'])).

thf('245',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k5_xboole_0 @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('246',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['243','246'])).

thf('248',plain,(
    ! [X8: $i] :
      ( ( k5_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('249',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['240','249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('255',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['217','252','253','254'])).

thf('256',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('257',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('258',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['256','258'])).

thf('260',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['259','261'])).

thf('263',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['255','262'])).

thf('264',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('265',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('266',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('267',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['265','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['264','268'])).

thf('270',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['263','269'])).

thf('271',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','270'])).

thf('272',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('274',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['272','273'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ll0PCDkR5U
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 45.72/45.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 45.72/45.98  % Solved by: fo/fo7.sh
% 45.72/45.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 45.72/45.98  % done 14649 iterations in 45.527s
% 45.72/45.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 45.72/45.98  % SZS output start Refutation
% 45.72/45.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 45.72/45.98  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 45.72/45.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 45.72/45.98  thf(sk_A_type, type, sk_A: $i).
% 45.72/45.98  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 45.72/45.98  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 45.72/45.98  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 45.72/45.98  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 45.72/45.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 45.72/45.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 45.72/45.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 45.72/45.98  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 45.72/45.98  thf(sk_B_type, type, sk_B: $i).
% 45.72/45.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 45.72/45.98  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 45.72/45.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 45.72/45.98  thf(d1_enumset1, axiom,
% 45.72/45.98    (![A:$i,B:$i,C:$i,D:$i]:
% 45.72/45.98     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 45.72/45.98       ( ![E:$i]:
% 45.72/45.98         ( ( r2_hidden @ E @ D ) <=>
% 45.72/45.98           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 45.72/45.98  thf(zf_stmt_0, axiom,
% 45.72/45.98    (![E:$i,C:$i,B:$i,A:$i]:
% 45.72/45.98     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 45.72/45.98       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 45.72/45.98  thf('0', plain,
% 45.72/45.98      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 45.72/45.98         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 45.72/45.98          | ((X15) = (X16))
% 45.72/45.98          | ((X15) = (X17))
% 45.72/45.98          | ((X15) = (X18)))),
% 45.72/45.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.72/45.98  thf(t21_xboole_1, axiom,
% 45.72/45.98    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 45.72/45.98  thf('1', plain,
% 45.72/45.98      (![X4 : $i, X5 : $i]:
% 45.72/45.98         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 45.72/45.98      inference('cnf', [status(esa)], [t21_xboole_1])).
% 45.72/45.98  thf(t100_xboole_1, axiom,
% 45.72/45.98    (![A:$i,B:$i]:
% 45.72/45.98     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 45.72/45.98  thf('2', plain,
% 45.72/45.98      (![X2 : $i, X3 : $i]:
% 45.72/45.98         ((k4_xboole_0 @ X2 @ X3)
% 45.72/45.98           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 45.72/45.98      inference('cnf', [status(esa)], [t100_xboole_1])).
% 45.72/45.98  thf('3', plain,
% 45.72/45.98      (![X0 : $i, X1 : $i]:
% 45.72/45.98         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 45.72/45.98           = (k5_xboole_0 @ X0 @ X0))),
% 45.72/45.98      inference('sup+', [status(thm)], ['1', '2'])).
% 45.72/45.98  thf(t46_xboole_1, axiom,
% 45.72/45.98    (![A:$i,B:$i]:
% 45.72/45.98     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 45.72/45.98  thf('4', plain,
% 45.72/45.98      (![X6 : $i, X7 : $i]:
% 45.72/45.98         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 45.72/45.98      inference('cnf', [status(esa)], [t46_xboole_1])).
% 45.72/45.98  thf('5', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.72/45.98      inference('sup+', [status(thm)], ['3', '4'])).
% 45.72/45.98  thf(t13_zfmisc_1, conjecture,
% 45.72/45.98    (![A:$i,B:$i]:
% 45.78/45.99     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 45.78/45.99         ( k1_tarski @ A ) ) =>
% 45.78/45.99       ( ( A ) = ( B ) ) ))).
% 45.78/45.99  thf(zf_stmt_1, negated_conjecture,
% 45.78/45.99    (~( ![A:$i,B:$i]:
% 45.78/45.99        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 45.78/45.99            ( k1_tarski @ A ) ) =>
% 45.78/45.99          ( ( A ) = ( B ) ) ) )),
% 45.78/45.99    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 45.78/45.99  thf('6', plain,
% 45.78/45.99      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 45.78/45.99         = (k1_tarski @ sk_A))),
% 45.78/45.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 45.78/45.99  thf(t98_xboole_1, axiom,
% 45.78/45.99    (![A:$i,B:$i]:
% 45.78/45.99     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 45.78/45.99  thf('7', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('8', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf(t91_xboole_1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i]:
% 45.78/45.99     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 45.78/45.99       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 45.78/45.99  thf('9', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('10', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['8', '9'])).
% 45.78/45.99  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('12', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['8', '9'])).
% 45.78/45.99  thf('13', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['11', '12'])).
% 45.78/45.99  thf(t5_boole, axiom,
% 45.78/45.99    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 45.78/45.99  thf('14', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('16', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('17', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['7', '16'])).
% 45.78/45.99  thf('18', plain,
% 45.78/45.99      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['6', '17'])).
% 45.78/45.99  thf('19', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('20', plain,
% 45.78/45.99      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['18', '19'])).
% 45.78/45.99  thf('21', plain,
% 45.78/45.99      (![X2 : $i, X3 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X2 @ X3)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 45.78/45.99  thf('22', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('23', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['21', '22'])).
% 45.78/45.99  thf('24', plain,
% 45.78/45.99      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['20', '23'])).
% 45.78/45.99  thf('25', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('26', plain,
% 45.78/45.99      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k1_tarski @ sk_B))),
% 45.78/45.99      inference('demod', [status(thm)], ['24', '25'])).
% 45.78/45.99  thf(commutativity_k3_xboole_0, axiom,
% 45.78/45.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 45.78/45.99  thf('27', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 45.78/45.99  thf('28', plain,
% 45.78/45.99      (![X2 : $i, X3 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X2 @ X3)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 45.78/45.99  thf('29', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['27', '28'])).
% 45.78/45.99  thf('30', plain,
% 45.78/45.99      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['26', '29'])).
% 45.78/45.99  thf('31', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('32', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['30', '31'])).
% 45.78/45.99  thf('33', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('34', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ 
% 45.78/45.99               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['32', '33'])).
% 45.78/45.99  thf('35', plain,
% 45.78/45.99      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 45.78/45.99         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['5', '34'])).
% 45.78/45.99  thf('36', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('37', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('38', plain,
% 45.78/45.99      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k1_tarski @ sk_A))),
% 45.78/45.99      inference('demod', [status(thm)], ['35', '36', '37'])).
% 45.78/45.99  thf(t71_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i]:
% 45.78/45.99     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 45.78/45.99  thf('39', plain,
% 45.78/45.99      (![X36 : $i, X37 : $i, X38 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 45.78/45.99           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 45.78/45.99      inference('cnf', [status(esa)], [t71_enumset1])).
% 45.78/45.99  thf(t70_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 45.78/45.99  thf('40', plain,
% 45.78/45.99      (![X34 : $i, X35 : $i]:
% 45.78/45.99         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 45.78/45.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 45.78/45.99  thf('41', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['39', '40'])).
% 45.78/45.99  thf(t74_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 45.78/45.99     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 45.78/45.99       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 45.78/45.99  thf('42', plain,
% 45.78/45.99      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 45.78/45.99           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 45.78/45.99      inference('cnf', [status(esa)], [t74_enumset1])).
% 45.78/45.99  thf(t73_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 45.78/45.99     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 45.78/45.99       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 45.78/45.99  thf('43', plain,
% 45.78/45.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 45.78/45.99         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 45.78/45.99           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 45.78/45.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 45.78/45.99  thf('44', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['42', '43'])).
% 45.78/45.99  thf('45', plain,
% 45.78/45.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 45.78/45.99         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 45.78/45.99           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 45.78/45.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 45.78/45.99  thf(t61_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 45.78/45.99     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 45.78/45.99       ( k2_xboole_0 @
% 45.78/45.99         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 45.78/45.99  thf('46', plain,
% 45.78/45.99      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 45.78/45.99           = (k2_xboole_0 @ 
% 45.78/45.99              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 45.78/45.99              (k1_tarski @ X32)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t61_enumset1])).
% 45.78/45.99  thf('47', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 45.78/45.99           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 45.78/45.99              (k1_tarski @ X5)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['45', '46'])).
% 45.78/45.99  thf('48', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 45.78/45.99              (k1_tarski @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['44', '47'])).
% 45.78/45.99  thf(t72_enumset1, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i,D:$i]:
% 45.78/45.99     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 45.78/45.99  thf('49', plain,
% 45.78/45.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 45.78/45.99           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 45.78/45.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 45.78/45.99  thf('50', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 45.78/45.99              (k1_tarski @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['48', '49'])).
% 45.78/45.99  thf('51', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 45.78/45.99           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['41', '50'])).
% 45.78/45.99  thf('52', plain,
% 45.78/45.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 45.78/45.99           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 45.78/45.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 45.78/45.99  thf('53', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 45.78/45.99           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 45.78/45.99      inference('demod', [status(thm)], ['51', '52'])).
% 45.78/45.99  thf(t69_enumset1, axiom,
% 45.78/45.99    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 45.78/45.99  thf('54', plain,
% 45.78/45.99      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 45.78/45.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 45.78/45.99  thf('55', plain,
% 45.78/45.99      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 45.78/45.99           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 45.78/45.99      inference('cnf', [status(esa)], [t74_enumset1])).
% 45.78/45.99  thf('56', plain,
% 45.78/45.99      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 45.78/45.99           = (k2_xboole_0 @ 
% 45.78/45.99              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 45.78/45.99              (k1_tarski @ X32)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t61_enumset1])).
% 45.78/45.99  thf('57', plain,
% 45.78/45.99      (![X4 : $i, X5 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 45.78/45.99      inference('cnf', [status(esa)], [t21_xboole_1])).
% 45.78/45.99  thf('58', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 45.78/45.99           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))
% 45.78/45.99           = (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1))),
% 45.78/45.99      inference('sup+', [status(thm)], ['56', '57'])).
% 45.78/45.99  thf('59', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 45.78/45.99           (k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6))
% 45.78/45.99           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['55', '58'])).
% 45.78/45.99  thf('60', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['21', '22'])).
% 45.78/45.99  thf('61', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('62', plain,
% 45.78/45.99      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['60', '61'])).
% 45.78/45.99  thf('63', plain,
% 45.78/45.99      (![X6 : $i, X7 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 45.78/45.99      inference('cnf', [status(esa)], [t46_xboole_1])).
% 45.78/45.99  thf('64', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['62', '63'])).
% 45.78/45.99  thf('65', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k5_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0) @ 
% 45.78/45.99           (k4_enumset1 @ X0 @ X0 @ X0 @ X0 @ X0 @ X0)) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['59', '64'])).
% 45.78/45.99  thf('66', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['42', '43'])).
% 45.78/45.99  thf('67', plain,
% 45.78/45.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 45.78/45.99           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 45.78/45.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 45.78/45.99  thf('68', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['66', '67'])).
% 45.78/45.99  thf('69', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['39', '40'])).
% 45.78/45.99  thf('70', plain,
% 45.78/45.99      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 45.78/45.99         ((k4_enumset1 @ X43 @ X43 @ X44 @ X45 @ X46 @ X47)
% 45.78/45.99           = (k3_enumset1 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 45.78/45.99      inference('cnf', [status(esa)], [t73_enumset1])).
% 45.78/45.99  thf('71', plain,
% 45.78/45.99      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 45.78/45.99         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 45.78/45.99           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 45.78/45.99      inference('cnf', [status(esa)], [t72_enumset1])).
% 45.78/45.99  thf('72', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['39', '40'])).
% 45.78/45.99  thf('73', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['65', '68', '69', '70', '71', '72'])).
% 45.78/45.99  thf('74', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['54', '73'])).
% 45.78/45.99  thf('75', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('76', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['74', '75'])).
% 45.78/45.99  thf('77', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('78', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('79', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k1_xboole_0)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))))),
% 45.78/45.99      inference('sup+', [status(thm)], ['77', '78'])).
% 45.78/45.99  thf('80', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('81', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['79', '80'])).
% 45.78/45.99  thf('82', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('83', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['81', '82'])).
% 45.78/45.99  thf('84', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('85', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('86', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('87', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k2_tarski @ X0 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['76', '85', '86'])).
% 45.78/45.99  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('89', plain,
% 45.78/45.99      (![X2 : $i, X3 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X2 @ X3)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t100_xboole_1])).
% 45.78/45.99  thf('90', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('91', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['89', '90'])).
% 45.78/45.99  thf('92', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['88', '91'])).
% 45.78/45.99  thf('93', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('94', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['92', '93'])).
% 45.78/45.99  thf('95', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('96', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('97', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['95', '96'])).
% 45.78/45.99  thf('98', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['94', '97'])).
% 45.78/45.99  thf('99', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('100', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['98', '99'])).
% 45.78/45.99  thf('101', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['27', '28'])).
% 45.78/45.99  thf('102', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('103', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['101', '102'])).
% 45.78/45.99  thf('104', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['100', '103'])).
% 45.78/45.99  thf('105', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('106', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['104', '105'])).
% 45.78/45.99  thf('107', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['95', '96'])).
% 45.78/45.99  thf('108', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X0 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['106', '107'])).
% 45.78/45.99  thf('109', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('110', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['108', '109'])).
% 45.78/45.99  thf('111', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('112', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['110', '111'])).
% 45.78/45.99  thf('113', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('115', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 45.78/45.99  thf('116', plain,
% 45.78/45.99      (![X6 : $i, X7 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 45.78/45.99      inference('cnf', [status(esa)], [t46_xboole_1])).
% 45.78/45.99  thf('117', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('118', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['116', '117'])).
% 45.78/45.99  thf('119', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('120', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 45.78/45.99           = (k2_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['118', '119'])).
% 45.78/45.99  thf('121', plain,
% 45.78/45.99      (![X4 : $i, X5 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 45.78/45.99      inference('cnf', [status(esa)], [t21_xboole_1])).
% 45.78/45.99  thf('122', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k2_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['120', '121'])).
% 45.78/45.99  thf('123', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 45.78/45.99           = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('sup+', [status(thm)], ['115', '122'])).
% 45.78/45.99  thf('124', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['7', '16'])).
% 45.78/45.99  thf('125', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['89', '90'])).
% 45.78/45.99  thf('126', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 45.78/45.99           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 45.78/45.99      inference('sup+', [status(thm)], ['124', '125'])).
% 45.78/45.99  thf('127', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2))
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 45.78/45.99              (k4_xboole_0 @ X2 @ 
% 45.78/45.99               (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0)))))),
% 45.78/45.99      inference('sup+', [status(thm)], ['123', '126'])).
% 45.78/45.99  thf('128', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 45.78/45.99  thf('129', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 45.78/45.99           = (k2_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['118', '119'])).
% 45.78/45.99  thf('130', plain,
% 45.78/45.99      (![X6 : $i, X7 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 45.78/45.99      inference('cnf', [status(esa)], [t46_xboole_1])).
% 45.78/45.99  thf('131', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['129', '130'])).
% 45.78/45.99  thf('132', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['128', '131'])).
% 45.78/45.99  thf('133', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('134', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 45.78/45.99  thf('135', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k2_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['120', '121'])).
% 45.78/45.99  thf('136', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('sup+', [status(thm)], ['134', '135'])).
% 45.78/45.99  thf('137', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['104', '105'])).
% 45.78/45.99  thf('138', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('139', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['137', '138'])).
% 45.78/45.99  thf('140', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('141', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['139', '140'])).
% 45.78/45.99  thf('142', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 45.78/45.99      inference('demod', [status(thm)], ['127', '132', '133', '136', '141'])).
% 45.78/45.99  thf('143', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['108', '109'])).
% 45.78/45.99  thf('144', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['142', '143'])).
% 45.78/45.99  thf('145', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ 
% 45.78/45.99            (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['87', '144'])).
% 45.78/45.99  thf('146', plain,
% 45.78/45.99      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 45.78/45.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 45.78/45.99  thf('147', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['65', '68', '69', '70', '71', '72'])).
% 45.78/45.99  thf('148', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['146', '147'])).
% 45.78/45.99  thf('149', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('150', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['148', '149'])).
% 45.78/45.99  thf('151', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('152', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('153', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k1_tarski @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['150', '151', '152'])).
% 45.78/45.99  thf('154', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['145', '153'])).
% 45.78/45.99  thf('155', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['108', '109'])).
% 45.78/45.99  thf('156', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['81', '82'])).
% 45.78/45.99  thf('157', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('158', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['30', '31'])).
% 45.78/45.99  thf('159', plain,
% 45.78/45.99      (((k5_xboole_0 @ 
% 45.78/45.99         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 45.78/45.99         (k1_tarski @ sk_B)) = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['157', '158'])).
% 45.78/45.99  thf('160', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('161', plain,
% 45.78/45.99      (((k5_xboole_0 @ 
% 45.78/45.99         (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 45.78/45.99         (k1_tarski @ sk_B)) = (k1_tarski @ sk_A))),
% 45.78/45.99      inference('demod', [status(thm)], ['159', '160'])).
% 45.78/45.99  thf('162', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('163', plain,
% 45.78/45.99      (((k1_tarski @ sk_B)
% 45.78/45.99         = (k5_xboole_0 @ 
% 45.78/45.99            (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 45.78/45.99            (k1_tarski @ sk_A)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['161', '162'])).
% 45.78/45.99  thf('164', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ 
% 45.78/45.99               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['32', '33'])).
% 45.78/45.99  thf('165', plain,
% 45.78/45.99      (((k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['163', '164'])).
% 45.78/45.99  thf('166', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('167', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['165', '166'])).
% 45.78/45.99  thf('168', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('169', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ (k1_tarski @ sk_A) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['30', '31'])).
% 45.78/45.99  thf('170', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ 
% 45.78/45.99           (k5_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 45.78/45.99           = (k5_xboole_0 @ 
% 45.78/45.99              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['167', '168', '169'])).
% 45.78/45.99  thf('171', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 45.78/45.99           = (k5_xboole_0 @ 
% 45.78/45.99              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 45.78/45.99              (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))))),
% 45.78/45.99      inference('sup+', [status(thm)], ['156', '170'])).
% 45.78/45.99  thf('172', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['10', '15'])).
% 45.78/45.99  thf('173', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 45.78/45.99           = (k5_xboole_0 @ 
% 45.78/45.99              (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['171', '172'])).
% 45.78/45.99  thf('174', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('175', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('176', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['174', '175'])).
% 45.78/45.99  thf('177', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X0 @ (k1_tarski @ sk_A)) @ X1)
% 45.78/45.99           = (k5_xboole_0 @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ 
% 45.78/45.99              (k5_xboole_0 @ 
% 45.78/45.99               (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ X1)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['173', '176'])).
% 45.78/45.99  thf('178', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['174', '175'])).
% 45.78/45.99  thf('179', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['174', '175'])).
% 45.78/45.99  thf('180', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['95', '96'])).
% 45.78/45.99  thf('181', plain,
% 45.78/45.99      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k1_tarski @ sk_A))),
% 45.78/45.99      inference('demod', [status(thm)], ['35', '36', '37'])).
% 45.78/45.99  thf('182', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ X0 @ X1))
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ X1)))),
% 45.78/45.99      inference('demod', [status(thm)], ['177', '178', '179', '180', '181'])).
% 45.78/45.99  thf('183', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X1 @ X0))))),
% 45.78/45.99      inference('sup+', [status(thm)], ['155', '182'])).
% 45.78/45.99  thf('184', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('185', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('186', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k1_tarski @ sk_A)
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 45.78/45.99              (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X1 @ X0))))),
% 45.78/45.99      inference('demod', [status(thm)], ['183', '184', '185'])).
% 45.78/45.99  thf('187', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('188', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['81', '82'])).
% 45.78/45.99  thf('189', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))
% 45.78/45.99           = (k5_xboole_0 @ X2 @ X1))),
% 45.78/45.99      inference('sup+', [status(thm)], ['187', '188'])).
% 45.78/45.99  thf('190', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k2_xboole_0 @ X0 @ X1)) @ 
% 45.78/45.99           (k5_xboole_0 @ X2 @ (k1_tarski @ sk_A)))
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['186', '189'])).
% 45.78/45.99  thf('191', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['174', '175'])).
% 45.78/45.99  thf('192', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['81', '82'])).
% 45.78/45.99  thf('193', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['190', '191', '192'])).
% 45.78/45.99  thf('194', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['154', '193'])).
% 45.78/45.99  thf('195', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('196', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ (k1_tarski @ X1)) @ 
% 45.78/45.99           (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ X0)) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['194', '195'])).
% 45.78/45.99  thf('197', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) @ 
% 45.78/45.99           (k2_enumset1 @ X1 @ X1 @ X1 @ X0)) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['53', '196'])).
% 45.78/45.99  thf('198', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['39', '40'])).
% 45.78/45.99  thf('199', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['190', '191', '192'])).
% 45.78/45.99  thf('200', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 45.78/45.99           (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['197', '198', '199'])).
% 45.78/45.99  thf('201', plain,
% 45.78/45.99      (((k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['38', '200'])).
% 45.78/45.99  thf('202', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['39', '40'])).
% 45.78/45.99  thf('203', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X3 @ X3 @ X3 @ X3 @ X2 @ X1 @ X0)
% 45.78/45.99           = (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['66', '67'])).
% 45.78/45.99  thf('204', plain,
% 45.78/45.99      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53)
% 45.78/45.99           = (k4_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53))),
% 45.78/45.99      inference('cnf', [status(esa)], [t74_enumset1])).
% 45.78/45.99  thf('205', plain,
% 45.78/45.99      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32)
% 45.78/45.99           = (k2_xboole_0 @ 
% 45.78/45.99              (k4_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31) @ 
% 45.78/45.99              (k1_tarski @ X32)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t61_enumset1])).
% 45.78/45.99  thf('206', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.78/45.99         ((k5_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 45.78/45.99           = (k2_xboole_0 @ (k5_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 45.78/45.99              (k1_tarski @ X6)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['204', '205'])).
% 45.78/45.99  thf('207', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['112', '113', '114'])).
% 45.78/45.99  thf('208', plain,
% 45.78/45.99      (![X4 : $i, X5 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (X4))),
% 45.78/45.99      inference('cnf', [status(esa)], [t21_xboole_1])).
% 45.78/45.99  thf('209', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['207', '208'])).
% 45.78/45.99  thf('210', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k1_tarski @ X0) @ 
% 45.78/45.99           (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)) = (k1_tarski @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['206', '209'])).
% 45.78/45.99  thf('211', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 45.78/45.99           = (k1_tarski @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['203', '210'])).
% 45.78/45.99  thf('212', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 45.78/45.99           = (k1_tarski @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['202', '211'])).
% 45.78/45.99  thf('213', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['27', '28'])).
% 45.78/45.99  thf('214', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['212', '213'])).
% 45.78/45.99  thf('215', plain,
% 45.78/45.99      (((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k1_tarski @ sk_A))
% 45.78/45.99         = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['201', '214'])).
% 45.78/45.99  thf('216', plain,
% 45.78/45.99      (![X12 : $i, X13 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X12 @ X13)
% 45.78/45.99           = (k5_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t98_xboole_1])).
% 45.78/45.99  thf('217', plain,
% 45.78/45.99      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_A))
% 45.78/45.99         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['215', '216'])).
% 45.78/45.99  thf('218', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 45.78/45.99           = (k1_tarski @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['202', '211'])).
% 45.78/45.99  thf('219', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['3', '4'])).
% 45.78/45.99  thf('220', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['101', '102'])).
% 45.78/45.99  thf('221', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['219', '220'])).
% 45.78/45.99  thf('222', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('223', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['221', '222'])).
% 45.78/45.99  thf('224', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)) @ 
% 45.78/45.99           (k1_tarski @ X0)) = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['218', '223'])).
% 45.78/45.99  thf('225', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('226', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ X1 @ X0)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['139', '140'])).
% 45.78/45.99  thf('227', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['224', '225', '226'])).
% 45.78/45.99  thf('228', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 45.78/45.99           = (k2_tarski @ X0 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['76', '85', '86'])).
% 45.78/45.99  thf('229', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['142', '143'])).
% 45.78/45.99  thf('230', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ 
% 45.78/45.99            (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['228', '229'])).
% 45.78/45.99  thf('231', plain,
% 45.78/45.99      (![X0 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 45.78/45.99           = (k1_tarski @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['150', '151', '152'])).
% 45.78/45.99  thf('232', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['230', '231'])).
% 45.78/45.99  thf('233', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ 
% 45.78/45.99           (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X0 @ X0)) @ 
% 45.78/45.99           (k2_tarski @ X1 @ X0)) = (k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['227', '232'])).
% 45.78/45.99  thf('234', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['190', '191', '192'])).
% 45.78/45.99  thf('235', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['104', '105'])).
% 45.78/45.99  thf('236', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 45.78/45.99      inference('demod', [status(thm)], ['81', '82'])).
% 45.78/45.99  thf('237', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 45.78/45.99           = (k4_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['235', '236'])).
% 45.78/45.99  thf('238', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('239', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 45.78/45.99           = (k4_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['237', '238'])).
% 45.78/45.99  thf('240', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X1 @ X0))
% 45.78/45.99           = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['233', '234', '239'])).
% 45.78/45.99  thf('241', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ 
% 45.78/45.99           (k2_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))) = (k1_xboole_0))),
% 45.78/45.99      inference('demod', [status(thm)], ['145', '153'])).
% 45.78/45.99  thf('242', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('demod', [status(thm)], ['190', '191', '192'])).
% 45.78/45.99  thf('243', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k1_xboole_0)
% 45.78/45.99           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_tarski @ X1 @ X1)) @ 
% 45.78/45.99              (k2_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['241', '242'])).
% 45.78/45.99  thf('244', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k4_xboole_0 @ X0 @ X1)
% 45.78/45.99           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['7', '16'])).
% 45.78/45.99  thf('245', plain,
% 45.78/45.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11)
% 45.78/45.99           = (k5_xboole_0 @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 45.78/45.99      inference('cnf', [status(esa)], [t91_xboole_1])).
% 45.78/45.99  thf('246', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 45.78/45.99           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)))),
% 45.78/45.99      inference('sup+', [status(thm)], ['244', '245'])).
% 45.78/45.99  thf('247', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ X0) @ 
% 45.78/45.99           (k2_xboole_0 @ (k1_tarski @ X1) @ X0))
% 45.78/45.99           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['243', '246'])).
% 45.78/45.99  thf('248', plain, (![X8 : $i]: ((k5_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 45.78/45.99      inference('cnf', [status(esa)], [t5_boole])).
% 45.78/45.99  thf('249', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X1) @ X0) @ 
% 45.78/45.99           (k2_xboole_0 @ (k1_tarski @ X1) @ X0)) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['247', '248'])).
% 45.78/45.99  thf('250', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k5_xboole_0 @ k1_xboole_0 @ 
% 45.78/45.99           (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))
% 45.78/45.99           = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['240', '249'])).
% 45.78/45.99  thf('251', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('252', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 45.78/45.99           = (k2_tarski @ X1 @ X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['250', '251'])).
% 45.78/45.99  thf('253', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 45.78/45.99      inference('sup+', [status(thm)], ['83', '84'])).
% 45.78/45.99  thf('254', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 45.78/45.99      inference('demod', [status(thm)], ['13', '14'])).
% 45.78/45.99  thf('255', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_A))),
% 45.78/45.99      inference('demod', [status(thm)], ['217', '252', '253', '254'])).
% 45.78/45.99  thf('256', plain,
% 45.78/45.99      (![X34 : $i, X35 : $i]:
% 45.78/45.99         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 45.78/45.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 45.78/45.99  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 45.78/45.99  thf(zf_stmt_3, axiom,
% 45.78/45.99    (![A:$i,B:$i,C:$i,D:$i]:
% 45.78/45.99     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 45.78/45.99       ( ![E:$i]:
% 45.78/45.99         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 45.78/45.99  thf('257', plain,
% 45.78/45.99      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 45.78/45.99         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 45.78/45.99          | (r2_hidden @ X19 @ X23)
% 45.78/45.99          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 45.78/45.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 45.78/45.99  thf('258', plain,
% 45.78/45.99      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 45.78/45.99         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 45.78/45.99          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 45.78/45.99      inference('simplify', [status(thm)], ['257'])).
% 45.78/45.99  thf('259', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 45.78/45.99          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 45.78/45.99      inference('sup+', [status(thm)], ['256', '258'])).
% 45.78/45.99  thf('260', plain,
% 45.78/45.99      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 45.78/45.99         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 45.78/45.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 45.78/45.99  thf('261', plain,
% 45.78/45.99      (![X14 : $i, X16 : $i, X17 : $i]:
% 45.78/45.99         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 45.78/45.99      inference('simplify', [status(thm)], ['260'])).
% 45.78/45.99  thf('262', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 45.78/45.99      inference('sup-', [status(thm)], ['259', '261'])).
% 45.78/45.99  thf('263', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 45.78/45.99      inference('sup+', [status(thm)], ['255', '262'])).
% 45.78/45.99  thf('264', plain,
% 45.78/45.99      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 45.78/45.99      inference('cnf', [status(esa)], [t69_enumset1])).
% 45.78/45.99  thf('265', plain,
% 45.78/45.99      (![X34 : $i, X35 : $i]:
% 45.78/45.99         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 45.78/45.99      inference('cnf', [status(esa)], [t70_enumset1])).
% 45.78/45.99  thf('266', plain,
% 45.78/45.99      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 45.78/45.99         (~ (r2_hidden @ X24 @ X23)
% 45.78/45.99          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 45.78/45.99          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 45.78/45.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 45.78/45.99  thf('267', plain,
% 45.78/45.99      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 45.78/45.99         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 45.78/45.99          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 45.78/45.99      inference('simplify', [status(thm)], ['266'])).
% 45.78/45.99  thf('268', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 45.78/45.99         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 45.78/45.99          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 45.78/45.99      inference('sup-', [status(thm)], ['265', '267'])).
% 45.78/45.99  thf('269', plain,
% 45.78/45.99      (![X0 : $i, X1 : $i]:
% 45.78/45.99         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 45.78/45.99          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 45.78/45.99      inference('sup-', [status(thm)], ['264', '268'])).
% 45.78/45.99  thf('270', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 45.78/45.99      inference('sup-', [status(thm)], ['263', '269'])).
% 45.78/45.99  thf('271', plain,
% 45.78/45.99      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 45.78/45.99      inference('sup-', [status(thm)], ['0', '270'])).
% 45.78/45.99  thf('272', plain, (((sk_B) = (sk_A))),
% 45.78/45.99      inference('simplify', [status(thm)], ['271'])).
% 45.78/45.99  thf('273', plain, (((sk_A) != (sk_B))),
% 45.78/45.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 45.78/45.99  thf('274', plain, ($false),
% 45.78/45.99      inference('simplify_reflect-', [status(thm)], ['272', '273'])).
% 45.78/45.99  
% 45.78/45.99  % SZS output end Refutation
% 45.78/45.99  
% 45.78/45.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
