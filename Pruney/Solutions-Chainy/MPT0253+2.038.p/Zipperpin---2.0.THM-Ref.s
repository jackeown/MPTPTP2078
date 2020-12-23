%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vvy7HuBM1l

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:35 EST 2020

% Result     : Theorem 3.47s
% Output     : Refutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 239 expanded)
%              Number of leaves         :   34 (  85 expanded)
%              Depth                    :   21
%              Number of atoms          :  862 (1794 expanded)
%              Number of equality atoms :   85 ( 179 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t48_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t48_zfmisc_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X39 @ X40 @ X41 ) @ ( k1_tarski @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('4',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('5',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X29: $i] :
      ( r1_tarski @ k1_xboole_0 @ X29 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ( X21 != X22 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X22: $i] :
      ( r1_tarski @ X22 @ X22 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ X13 @ X10 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ X13 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X26: $i] :
      ( ( k2_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','50'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('54',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X37 @ X36 ) @ ( k2_tarski @ X38 @ X36 ) )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('55',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('56',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X37 @ X36 @ X38 @ X36 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( k2_enumset1 @ X46 @ X46 @ X47 @ X48 )
      = ( k1_enumset1 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X1 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('61',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X43: $i] :
      ( ( k2_tarski @ X43 @ X43 )
      = ( k1_tarski @ X43 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','65'])).

thf('67',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('71',plain,(
    ! [X63: $i,X65: $i,X66: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X63 @ X65 ) @ X66 )
      | ~ ( r2_hidden @ X65 @ X66 )
      | ~ ( r2_hidden @ X63 @ X66 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('75',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = ( k2_tarski @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('77',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C_2 ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k2_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X30 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('81',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X26: $i] :
      ( ( k2_xboole_0 @ X26 @ k1_xboole_0 )
      = X26 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('83',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['0','68','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vvy7HuBM1l
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:01:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.47/3.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.47/3.73  % Solved by: fo/fo7.sh
% 3.47/3.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.47/3.73  % done 6450 iterations in 3.285s
% 3.47/3.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.47/3.73  % SZS output start Refutation
% 3.47/3.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.47/3.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.47/3.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.47/3.73  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.47/3.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.47/3.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.47/3.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.47/3.73  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.47/3.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.47/3.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.47/3.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.47/3.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.47/3.73  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.47/3.73  thf(sk_A_type, type, sk_A: $i).
% 3.47/3.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.47/3.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.47/3.73  thf(t48_zfmisc_1, conjecture,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 3.47/3.73       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 3.47/3.73  thf(zf_stmt_0, negated_conjecture,
% 3.47/3.73    (~( ![A:$i,B:$i,C:$i]:
% 3.47/3.73        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 3.47/3.73          ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ) )),
% 3.47/3.73    inference('cnf.neg', [status(esa)], [t48_zfmisc_1])).
% 3.47/3.73  thf('0', plain,
% 3.47/3.73      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) != (sk_B_1))),
% 3.47/3.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.47/3.73  thf(t70_enumset1, axiom,
% 3.47/3.73    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.47/3.73  thf('1', plain,
% 3.47/3.73      (![X44 : $i, X45 : $i]:
% 3.47/3.73         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 3.47/3.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.47/3.73  thf(t46_enumset1, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i,D:$i]:
% 3.47/3.73     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.47/3.73       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 3.47/3.73  thf('2', plain,
% 3.47/3.73      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X39 @ X40 @ X41 @ X42)
% 3.47/3.73           = (k2_xboole_0 @ (k1_enumset1 @ X39 @ X40 @ X41) @ (k1_tarski @ X42)))),
% 3.47/3.73      inference('cnf', [status(esa)], [t46_enumset1])).
% 3.47/3.73  thf('3', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 3.47/3.73           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['1', '2'])).
% 3.47/3.73  thf(t71_enumset1, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.47/3.73  thf('4', plain,
% 3.47/3.73      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 3.47/3.73           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 3.47/3.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.47/3.73  thf('5', plain,
% 3.47/3.73      (![X44 : $i, X45 : $i]:
% 3.47/3.73         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 3.47/3.73      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.47/3.73  thf(l51_zfmisc_1, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.47/3.73  thf('6', plain,
% 3.47/3.73      (![X61 : $i, X62 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 3.47/3.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.47/3.73  thf('7', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['5', '6'])).
% 3.47/3.73  thf('8', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 3.47/3.73           = (k2_xboole_0 @ X1 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['4', '7'])).
% 3.47/3.73  thf('9', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))
% 3.47/3.73           = (k2_xboole_0 @ X1 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['3', '8'])).
% 3.47/3.73  thf(t69_enumset1, axiom,
% 3.47/3.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.47/3.73  thf('10', plain,
% 3.47/3.73      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 3.47/3.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.47/3.73  thf('11', plain,
% 3.47/3.73      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 3.47/3.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.47/3.73  thf('12', plain,
% 3.47/3.73      (![X61 : $i, X62 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 3.47/3.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.47/3.73  thf('13', plain,
% 3.47/3.73      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['11', '12'])).
% 3.47/3.73  thf(t2_tarski, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 3.47/3.73       ( ( A ) = ( B ) ) ))).
% 3.47/3.73  thf('14', plain,
% 3.47/3.73      (![X15 : $i, X16 : $i]:
% 3.47/3.73         (((X16) = (X15))
% 3.47/3.73          | (r2_hidden @ (sk_C @ X15 @ X16) @ X15)
% 3.47/3.73          | (r2_hidden @ (sk_C @ X15 @ X16) @ X16))),
% 3.47/3.73      inference('cnf', [status(esa)], [t2_tarski])).
% 3.47/3.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.47/3.73  thf('15', plain, (![X29 : $i]: (r1_tarski @ k1_xboole_0 @ X29)),
% 3.47/3.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.47/3.73  thf(t28_xboole_1, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.47/3.73  thf('16', plain,
% 3.47/3.73      (![X27 : $i, X28 : $i]:
% 3.47/3.73         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 3.47/3.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.47/3.73  thf('17', plain,
% 3.47/3.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['15', '16'])).
% 3.47/3.73  thf(t100_xboole_1, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.47/3.73  thf('18', plain,
% 3.47/3.73      (![X24 : $i, X25 : $i]:
% 3.47/3.73         ((k4_xboole_0 @ X24 @ X25)
% 3.47/3.73           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 3.47/3.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.47/3.73  thf('19', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.47/3.73           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['17', '18'])).
% 3.47/3.73  thf(d10_xboole_0, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.47/3.73  thf('20', plain,
% 3.47/3.73      (![X21 : $i, X22 : $i]: ((r1_tarski @ X21 @ X22) | ((X21) != (X22)))),
% 3.47/3.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.47/3.73  thf('21', plain, (![X22 : $i]: (r1_tarski @ X22 @ X22)),
% 3.47/3.73      inference('simplify', [status(thm)], ['20'])).
% 3.47/3.73  thf('22', plain,
% 3.47/3.73      (![X27 : $i, X28 : $i]:
% 3.47/3.73         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 3.47/3.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.47/3.73  thf('23', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['21', '22'])).
% 3.47/3.73  thf('24', plain,
% 3.47/3.73      (![X24 : $i, X25 : $i]:
% 3.47/3.73         ((k4_xboole_0 @ X24 @ X25)
% 3.47/3.73           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 3.47/3.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.47/3.73  thf('25', plain,
% 3.47/3.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['23', '24'])).
% 3.47/3.73  thf(d5_xboole_0, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.47/3.73       ( ![D:$i]:
% 3.47/3.73         ( ( r2_hidden @ D @ C ) <=>
% 3.47/3.73           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.47/3.73  thf('26', plain,
% 3.47/3.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X13 @ X12)
% 3.47/3.73          | ~ (r2_hidden @ X13 @ X11)
% 3.47/3.73          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 3.47/3.73      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.47/3.73  thf('27', plain,
% 3.47/3.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X13 @ X11)
% 3.47/3.73          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 3.47/3.73      inference('simplify', [status(thm)], ['26'])).
% 3.47/3.73  thf('28', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 3.47/3.73          | ~ (r2_hidden @ X1 @ X0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['25', '27'])).
% 3.47/3.73  thf('29', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 3.47/3.73          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['19', '28'])).
% 3.47/3.73  thf('30', plain,
% 3.47/3.73      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['15', '16'])).
% 3.47/3.73  thf(d4_xboole_0, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 3.47/3.73       ( ![D:$i]:
% 3.47/3.73         ( ( r2_hidden @ D @ C ) <=>
% 3.47/3.73           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.47/3.73  thf('31', plain,
% 3.47/3.73      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X7 @ X6)
% 3.47/3.73          | (r2_hidden @ X7 @ X5)
% 3.47/3.73          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 3.47/3.73      inference('cnf', [status(esa)], [d4_xboole_0])).
% 3.47/3.73  thf('32', plain,
% 3.47/3.73      (![X4 : $i, X5 : $i, X7 : $i]:
% 3.47/3.73         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 3.47/3.73      inference('simplify', [status(thm)], ['31'])).
% 3.47/3.73  thf('33', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['30', '32'])).
% 3.47/3.73  thf('34', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 3.47/3.73      inference('clc', [status(thm)], ['29', '33'])).
% 3.47/3.73  thf('35', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0) | ((X0) = (k1_xboole_0)))),
% 3.47/3.73      inference('sup-', [status(thm)], ['14', '34'])).
% 3.47/3.73  thf('36', plain,
% 3.47/3.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['23', '24'])).
% 3.47/3.73  thf('37', plain,
% 3.47/3.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X13 @ X12)
% 3.47/3.73          | (r2_hidden @ X13 @ X10)
% 3.47/3.73          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 3.47/3.73      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.47/3.73  thf('38', plain,
% 3.47/3.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 3.47/3.73         ((r2_hidden @ X13 @ X10)
% 3.47/3.73          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 3.47/3.73      inference('simplify', [status(thm)], ['37'])).
% 3.47/3.73  thf('39', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['36', '38'])).
% 3.47/3.73  thf('40', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 3.47/3.73          | ~ (r2_hidden @ X1 @ X0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['25', '27'])).
% 3.47/3.73  thf('41', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('clc', [status(thm)], ['39', '40'])).
% 3.47/3.73  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['35', '41'])).
% 3.47/3.73  thf('43', plain,
% 3.47/3.73      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['23', '24'])).
% 3.47/3.73  thf(t39_xboole_1, axiom,
% 3.47/3.73    (![A:$i,B:$i]:
% 3.47/3.73     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.47/3.73  thf('44', plain,
% 3.47/3.73      (![X30 : $i, X31 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 3.47/3.73           = (k2_xboole_0 @ X30 @ X31))),
% 3.47/3.73      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.47/3.73  thf('45', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 3.47/3.73           = (k2_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['43', '44'])).
% 3.47/3.73  thf('46', plain,
% 3.47/3.73      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['11', '12'])).
% 3.47/3.73  thf('47', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 3.47/3.73           = (k3_tarski @ (k1_tarski @ X0)))),
% 3.47/3.73      inference('demod', [status(thm)], ['45', '46'])).
% 3.47/3.73  thf('48', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k3_tarski @ (k1_tarski @ X0)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['42', '47'])).
% 3.47/3.73  thf(t1_boole, axiom,
% 3.47/3.73    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.47/3.73  thf('49', plain, (![X26 : $i]: ((k2_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 3.47/3.73      inference('cnf', [status(esa)], [t1_boole])).
% 3.47/3.73  thf('50', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['48', '49'])).
% 3.47/3.73  thf('51', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 3.47/3.73      inference('demod', [status(thm)], ['13', '50'])).
% 3.47/3.73  thf(l53_enumset1, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i,D:$i]:
% 3.47/3.73     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 3.47/3.73       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 3.47/3.73  thf('52', plain,
% 3.47/3.73      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 3.47/3.73           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k2_tarski @ X34 @ X35)))),
% 3.47/3.73      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.47/3.73  thf('53', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['51', '52'])).
% 3.47/3.73  thf(t137_enumset1, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 3.47/3.73       ( k1_enumset1 @ A @ B @ C ) ))).
% 3.47/3.73  thf('54', plain,
% 3.47/3.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ (k2_tarski @ X37 @ X36) @ (k2_tarski @ X38 @ X36))
% 3.47/3.73           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 3.47/3.73      inference('cnf', [status(esa)], [t137_enumset1])).
% 3.47/3.73  thf('55', plain,
% 3.47/3.73      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 3.47/3.73           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k2_tarski @ X34 @ X35)))),
% 3.47/3.73      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.47/3.73  thf('56', plain,
% 3.47/3.73      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X37 @ X36 @ X38 @ X36)
% 3.47/3.73           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 3.47/3.73      inference('demod', [status(thm)], ['54', '55'])).
% 3.47/3.73  thf('57', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k2_tarski @ X1 @ X0) = (k1_enumset1 @ X0 @ X1 @ X1))),
% 3.47/3.73      inference('sup+', [status(thm)], ['53', '56'])).
% 3.47/3.73  thf('58', plain,
% 3.47/3.73      (![X46 : $i, X47 : $i, X48 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X46 @ X46 @ X47 @ X48)
% 3.47/3.73           = (k1_enumset1 @ X46 @ X47 @ X48))),
% 3.47/3.73      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.47/3.73  thf('59', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X0 @ X0 @ X1 @ X1) = (k2_tarski @ X1 @ X0))),
% 3.47/3.73      inference('sup+', [status(thm)], ['57', '58'])).
% 3.47/3.73  thf('60', plain,
% 3.47/3.73      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 3.47/3.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.47/3.73  thf('61', plain,
% 3.47/3.73      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 3.47/3.73           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k2_tarski @ X34 @ X35)))),
% 3.47/3.73      inference('cnf', [status(esa)], [l53_enumset1])).
% 3.47/3.73  thf('62', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.47/3.73         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 3.47/3.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['60', '61'])).
% 3.47/3.73  thf('63', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k2_tarski @ X1 @ X0)
% 3.47/3.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X1)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['59', '62'])).
% 3.47/3.73  thf('64', plain,
% 3.47/3.73      (![X43 : $i]: ((k2_tarski @ X43 @ X43) = (k1_tarski @ X43))),
% 3.47/3.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.47/3.73  thf('65', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k2_tarski @ X1 @ X0)
% 3.47/3.73           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 3.47/3.73      inference('demod', [status(thm)], ['63', '64'])).
% 3.47/3.73  thf('66', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_tarski @ X0 @ X1)) = (k2_xboole_0 @ X1 @ X0))),
% 3.47/3.73      inference('demod', [status(thm)], ['9', '10', '65'])).
% 3.47/3.73  thf('67', plain,
% 3.47/3.73      (![X61 : $i, X62 : $i]:
% 3.47/3.73         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 3.47/3.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.47/3.73  thf('68', plain,
% 3.47/3.73      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.47/3.73      inference('sup+', [status(thm)], ['66', '67'])).
% 3.47/3.73  thf('69', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 3.47/3.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.47/3.73  thf('70', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 3.47/3.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.47/3.73  thf(t38_zfmisc_1, axiom,
% 3.47/3.73    (![A:$i,B:$i,C:$i]:
% 3.47/3.73     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 3.47/3.73       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 3.47/3.73  thf('71', plain,
% 3.47/3.73      (![X63 : $i, X65 : $i, X66 : $i]:
% 3.47/3.73         ((r1_tarski @ (k2_tarski @ X63 @ X65) @ X66)
% 3.47/3.73          | ~ (r2_hidden @ X65 @ X66)
% 3.47/3.73          | ~ (r2_hidden @ X63 @ X66))),
% 3.47/3.73      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.47/3.73  thf('72', plain,
% 3.47/3.73      (![X0 : $i]:
% 3.47/3.73         (~ (r2_hidden @ X0 @ sk_B_1)
% 3.47/3.73          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_B_1))),
% 3.47/3.73      inference('sup-', [status(thm)], ['70', '71'])).
% 3.47/3.73  thf('73', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)),
% 3.47/3.73      inference('sup-', [status(thm)], ['69', '72'])).
% 3.47/3.73  thf('74', plain,
% 3.47/3.73      (![X27 : $i, X28 : $i]:
% 3.47/3.73         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 3.47/3.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 3.47/3.73  thf('75', plain,
% 3.47/3.73      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 3.47/3.73         = (k2_tarski @ sk_A @ sk_C_2))),
% 3.47/3.73      inference('sup-', [status(thm)], ['73', '74'])).
% 3.47/3.73  thf('76', plain,
% 3.47/3.73      (![X24 : $i, X25 : $i]:
% 3.47/3.73         ((k4_xboole_0 @ X24 @ X25)
% 3.47/3.73           = (k5_xboole_0 @ X24 @ (k3_xboole_0 @ X24 @ X25)))),
% 3.47/3.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.47/3.73  thf('77', plain,
% 3.47/3.73      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1)
% 3.47/3.73         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ 
% 3.47/3.73            (k2_tarski @ sk_A @ sk_C_2)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['75', '76'])).
% 3.47/3.73  thf('78', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.47/3.73      inference('sup-', [status(thm)], ['35', '41'])).
% 3.47/3.73  thf('79', plain,
% 3.47/3.73      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C_2) @ sk_B_1) = (k1_xboole_0))),
% 3.47/3.73      inference('demod', [status(thm)], ['77', '78'])).
% 3.47/3.73  thf('80', plain,
% 3.47/3.73      (![X30 : $i, X31 : $i]:
% 3.47/3.73         ((k2_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X30))
% 3.47/3.73           = (k2_xboole_0 @ X30 @ X31))),
% 3.47/3.73      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.47/3.73  thf('81', plain,
% 3.47/3.73      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 3.47/3.73         = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 3.47/3.73      inference('sup+', [status(thm)], ['79', '80'])).
% 3.47/3.73  thf('82', plain, (![X26 : $i]: ((k2_xboole_0 @ X26 @ k1_xboole_0) = (X26))),
% 3.47/3.73      inference('cnf', [status(esa)], [t1_boole])).
% 3.47/3.73  thf('83', plain,
% 3.47/3.73      (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_C_2)))),
% 3.47/3.73      inference('demod', [status(thm)], ['81', '82'])).
% 3.47/3.73  thf('84', plain, (((sk_B_1) != (sk_B_1))),
% 3.47/3.73      inference('demod', [status(thm)], ['0', '68', '83'])).
% 3.47/3.73  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 3.47/3.73  
% 3.47/3.73  % SZS output end Refutation
% 3.47/3.73  
% 3.60/3.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
