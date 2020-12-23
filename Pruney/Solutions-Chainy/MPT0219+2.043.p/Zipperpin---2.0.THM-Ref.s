%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqnT1sneVH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:09 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 634 expanded)
%              Number of leaves         :   30 ( 219 expanded)
%              Depth                    :   29
%              Number of atoms          :  863 (4296 expanded)
%              Number of equality atoms :  105 ( 529 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( X25 = X26 )
      | ( X25 = X27 )
      | ( X25 = X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('10',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['21','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','68'])).

thf('70',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('73',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('77',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('78',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('79',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','80'])).

thf('82',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('83',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('84',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('85',plain,(
    ! [X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ X34 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','86'])).

thf('88',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,
    ( ( sk_B = sk_A )
    | ( sk_B = sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['0','88'])).

thf('90',plain,(
    sk_B = sk_A ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqnT1sneVH
% 0.16/0.36  % Computer   : n001.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 20:28:45 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.57/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.76  % Solved by: fo/fo7.sh
% 0.57/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.76  % done 647 iterations in 0.282s
% 0.57/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.76  % SZS output start Refutation
% 0.57/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.57/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.57/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.57/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.57/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.76  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.57/0.76  thf(d1_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.76       ( ![E:$i]:
% 0.57/0.76         ( ( r2_hidden @ E @ D ) <=>
% 0.57/0.76           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.57/0.76  thf(zf_stmt_0, axiom,
% 0.57/0.76    (![E:$i,C:$i,B:$i,A:$i]:
% 0.57/0.76     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.57/0.76       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.57/0.76  thf('0', plain,
% 0.57/0.76      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.57/0.76         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 0.57/0.76          | ((X25) = (X26))
% 0.57/0.76          | ((X25) = (X27))
% 0.57/0.76          | ((X25) = (X28)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf(t69_enumset1, axiom,
% 0.57/0.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.57/0.76  thf('1', plain, (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.57/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.57/0.76  thf(t70_enumset1, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.57/0.76  thf('2', plain,
% 0.57/0.76      (![X37 : $i, X38 : $i]:
% 0.57/0.76         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.57/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.57/0.76  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.57/0.76  thf(zf_stmt_2, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.76     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.57/0.76       ( ![E:$i]:
% 0.57/0.76         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.57/0.76  thf('3', plain,
% 0.57/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.57/0.76         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.57/0.76          | (r2_hidden @ X29 @ X33)
% 0.57/0.76          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.76  thf('4', plain,
% 0.57/0.76      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.57/0.76         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.57/0.76          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.57/0.76      inference('simplify', [status(thm)], ['3'])).
% 0.57/0.76  thf('5', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.57/0.76          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.57/0.76      inference('sup+', [status(thm)], ['2', '4'])).
% 0.57/0.76  thf('6', plain,
% 0.57/0.76      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.57/0.76         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.76  thf('7', plain,
% 0.57/0.76      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.57/0.76         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.57/0.76      inference('simplify', [status(thm)], ['6'])).
% 0.57/0.76  thf('8', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.57/0.76      inference('sup-', [status(thm)], ['5', '7'])).
% 0.57/0.76  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['1', '8'])).
% 0.57/0.76  thf(t13_zfmisc_1, conjecture,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.76         ( k1_tarski @ A ) ) =>
% 0.57/0.76       ( ( A ) = ( B ) ) ))).
% 0.57/0.76  thf(zf_stmt_3, negated_conjecture,
% 0.57/0.76    (~( ![A:$i,B:$i]:
% 0.57/0.76        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.57/0.76            ( k1_tarski @ A ) ) =>
% 0.57/0.76          ( ( A ) = ( B ) ) ) )),
% 0.57/0.76    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 0.57/0.76  thf('10', plain,
% 0.57/0.76      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.57/0.76         = (k1_tarski @ sk_A))),
% 0.57/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.57/0.76  thf(t98_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.57/0.76  thf('11', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ X22 @ X23)
% 0.57/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.76  thf(d10_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.76  thf('12', plain,
% 0.57/0.76      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.57/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.76  thf('13', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.57/0.76      inference('simplify', [status(thm)], ['12'])).
% 0.57/0.76  thf(t28_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.57/0.76  thf('14', plain,
% 0.57/0.76      (![X14 : $i, X15 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.57/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.76  thf('15', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.57/0.76  thf(commutativity_k3_xboole_0, axiom,
% 0.57/0.76    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.57/0.76  thf('16', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.76  thf(t100_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.57/0.76  thf('17', plain,
% 0.57/0.76      (![X11 : $i, X12 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X11 @ X12)
% 0.57/0.76           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.76  thf('18', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.76  thf('19', plain,
% 0.57/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['15', '18'])).
% 0.57/0.76  thf(t91_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i,C:$i]:
% 0.57/0.76     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.57/0.76       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.57/0.76  thf('20', plain,
% 0.57/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.57/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.57/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.76  thf('21', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.57/0.76           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['19', '20'])).
% 0.57/0.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.57/0.76  thf('22', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.57/0.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.57/0.76  thf('23', plain,
% 0.57/0.76      (![X14 : $i, X15 : $i]:
% 0.57/0.76         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.57/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.57/0.76  thf('24', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.76  thf('25', plain,
% 0.57/0.76      (![X11 : $i, X12 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X11 @ X12)
% 0.57/0.76           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.76  thf('26', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.76           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['24', '25'])).
% 0.57/0.76  thf('27', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.76  thf('28', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.57/0.76           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['16', '17'])).
% 0.57/0.76  thf('29', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['27', '28'])).
% 0.57/0.76  thf('30', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.76           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['26', '29'])).
% 0.57/0.76  thf(t48_xboole_1, axiom,
% 0.57/0.76    (![A:$i,B:$i]:
% 0.57/0.76     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.57/0.76  thf('31', plain,
% 0.57/0.76      (![X17 : $i, X18 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.57/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.76  thf('32', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.76           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['26', '29'])).
% 0.57/0.76  thf('33', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.57/0.76           = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['31', '32'])).
% 0.57/0.76  thf('34', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.76  thf('35', plain,
% 0.57/0.76      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['33', '34'])).
% 0.57/0.76  thf('36', plain,
% 0.57/0.76      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['30', '35'])).
% 0.57/0.76  thf('37', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ X22 @ X23)
% 0.57/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.76  thf('38', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['36', '37'])).
% 0.57/0.76  thf(t1_boole, axiom,
% 0.57/0.76    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.57/0.76  thf('39', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.57/0.76      inference('cnf', [status(esa)], [t1_boole])).
% 0.57/0.76  thf('40', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['38', '39'])).
% 0.57/0.76  thf('41', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['27', '28'])).
% 0.57/0.76  thf('42', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['40', '41'])).
% 0.57/0.76  thf('43', plain,
% 0.57/0.76      (![X17 : $i, X18 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.57/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.57/0.76  thf('44', plain,
% 0.57/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['42', '43'])).
% 0.57/0.76  thf('45', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.76  thf('46', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.57/0.76      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.57/0.76  thf('47', plain,
% 0.57/0.76      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['45', '46'])).
% 0.57/0.76  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['44', '47'])).
% 0.57/0.76  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['40', '41'])).
% 0.57/0.76  thf('50', plain,
% 0.57/0.76      (![X22 : $i, X23 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ X22 @ X23)
% 0.57/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.57/0.76  thf('51', plain,
% 0.57/0.76      (![X0 : $i]:
% 0.57/0.76         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['49', '50'])).
% 0.57/0.76  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.57/0.76      inference('demod', [status(thm)], ['44', '47'])).
% 0.57/0.76  thf('53', plain,
% 0.57/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.57/0.76      inference('sup+', [status(thm)], ['15', '18'])).
% 0.57/0.76  thf('54', plain,
% 0.57/0.76      (![X11 : $i, X12 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X11 @ X12)
% 0.57/0.76           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.57/0.76  thf('55', plain,
% 0.57/0.76      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.57/0.76         ((k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ X21)
% 0.57/0.76           = (k5_xboole_0 @ X19 @ (k5_xboole_0 @ X20 @ X21)))),
% 0.57/0.76      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.57/0.76  thf('56', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.57/0.76         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.57/0.76           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)))),
% 0.57/0.76      inference('sup+', [status(thm)], ['54', '55'])).
% 0.57/0.76  thf('57', plain,
% 0.57/0.76      (![X0 : $i, X1 : $i]:
% 0.57/0.76         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.57/0.76           = (k5_xboole_0 @ X1 @ 
% 0.57/0.76              (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))))),
% 0.57/0.76      inference('sup+', [status(thm)], ['53', '56'])).
% 0.57/0.76  thf('58', plain,
% 0.57/0.76      (![X17 : $i, X18 : $i]:
% 0.57/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.57/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.57/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.76  thf('59', plain,
% 0.60/0.76      (![X22 : $i, X23 : $i]:
% 0.60/0.76         ((k2_xboole_0 @ X22 @ X23)
% 0.60/0.76           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.60/0.76      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.60/0.76  thf('60', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.76           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['58', '59'])).
% 0.60/0.76  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['44', '47'])).
% 0.60/0.76  thf('62', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 0.60/0.76           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.60/0.76  thf('63', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['38', '39'])).
% 0.60/0.76  thf('64', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.60/0.76      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.76  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.60/0.76      inference('sup+', [status(thm)], ['52', '64'])).
% 0.60/0.76  thf('66', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.60/0.76      inference('demod', [status(thm)], ['51', '65'])).
% 0.60/0.76  thf('67', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((X1) = (k5_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.60/0.76      inference('sup+', [status(thm)], ['48', '66'])).
% 0.60/0.76  thf('68', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 0.60/0.76      inference('demod', [status(thm)], ['21', '67'])).
% 0.60/0.76  thf('69', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((k4_xboole_0 @ X0 @ X1)
% 0.60/0.76           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['11', '68'])).
% 0.60/0.76  thf('70', plain,
% 0.60/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.60/0.76         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['10', '69'])).
% 0.60/0.76  thf('71', plain,
% 0.60/0.76      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.60/0.76      inference('sup+', [status(thm)], ['15', '18'])).
% 0.60/0.76  thf('72', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['44', '47'])).
% 0.60/0.76  thf('73', plain,
% 0.60/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.60/0.76  thf('74', plain,
% 0.60/0.76      (![X17 : $i, X18 : $i]:
% 0.60/0.76         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.60/0.76           = (k3_xboole_0 @ X17 @ X18))),
% 0.60/0.76      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.60/0.76  thf('75', plain,
% 0.60/0.76      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.60/0.76         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.60/0.76      inference('sup+', [status(thm)], ['73', '74'])).
% 0.60/0.76  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.60/0.76      inference('sup+', [status(thm)], ['40', '41'])).
% 0.60/0.76  thf('77', plain,
% 0.60/0.76      (((k1_tarski @ sk_B)
% 0.60/0.76         = (k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['75', '76'])).
% 0.60/0.76  thf(d4_xboole_0, axiom,
% 0.60/0.76    (![A:$i,B:$i,C:$i]:
% 0.60/0.76     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.60/0.76       ( ![D:$i]:
% 0.60/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.76           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.76  thf('78', plain,
% 0.60/0.76      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.76         (~ (r2_hidden @ X6 @ X5)
% 0.60/0.76          | (r2_hidden @ X6 @ X4)
% 0.60/0.76          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.60/0.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.60/0.76  thf('79', plain,
% 0.60/0.76      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.60/0.76         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.60/0.76      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.76  thf('80', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.60/0.76          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['77', '79'])).
% 0.60/0.76  thf('81', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['9', '80'])).
% 0.60/0.76  thf('82', plain,
% 0.60/0.76      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 0.60/0.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.76  thf('83', plain,
% 0.60/0.76      (![X37 : $i, X38 : $i]:
% 0.60/0.76         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 0.60/0.76      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.60/0.76  thf('84', plain,
% 0.60/0.76      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.76         (~ (r2_hidden @ X34 @ X33)
% 0.60/0.76          | ~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.60/0.76          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.76  thf('85', plain,
% 0.60/0.76      (![X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.60/0.76         (~ (zip_tseitin_0 @ X34 @ X30 @ X31 @ X32)
% 0.60/0.76          | ~ (r2_hidden @ X34 @ (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.60/0.76      inference('simplify', [status(thm)], ['84'])).
% 0.60/0.76  thf('86', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.76         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.60/0.76          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.60/0.76      inference('sup-', [status(thm)], ['83', '85'])).
% 0.60/0.76  thf('87', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.60/0.76          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['82', '86'])).
% 0.60/0.76  thf('88', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A @ sk_A @ sk_A)),
% 0.60/0.76      inference('sup-', [status(thm)], ['81', '87'])).
% 0.60/0.76  thf('89', plain,
% 0.60/0.76      ((((sk_B) = (sk_A)) | ((sk_B) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['0', '88'])).
% 0.60/0.76  thf('90', plain, (((sk_B) = (sk_A))),
% 0.60/0.76      inference('simplify', [status(thm)], ['89'])).
% 0.60/0.76  thf('91', plain, (((sk_A) != (sk_B))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.76  thf('92', plain, ($false),
% 0.60/0.76      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.60/0.76  
% 0.60/0.76  % SZS output end Refutation
% 0.60/0.76  
% 0.60/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
