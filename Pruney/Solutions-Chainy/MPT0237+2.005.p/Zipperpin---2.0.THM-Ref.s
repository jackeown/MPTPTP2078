%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d9ziASn387

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:59 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 501 expanded)
%              Number of leaves         :   29 ( 172 expanded)
%              Depth                    :   20
%              Number of atoms          : 1013 (4201 expanded)
%              Number of equality atoms :  120 ( 497 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X56 @ X57 ) )
      = ( k2_xboole_0 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X58 ) @ ( k1_tarski @ X59 ) )
        = ( k2_tarski @ X58 @ X59 ) )
      | ( X58 = X59 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k5_xboole_0 @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('21',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k3_xboole_0 @ X55 @ ( k1_tarski @ X54 ) )
        = ( k1_tarski @ X54 ) )
      | ~ ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k3_xboole_0 @ X55 @ ( k1_tarski @ X54 ) )
        = ( k1_tarski @ X54 ) )
      | ~ ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','55'])).

thf('57',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( k5_xboole_0 @ X11 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('67',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['37','56','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['13','73'])).

thf('75',plain,(
    ! [X58: $i,X59: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X58 ) @ ( k1_tarski @ X59 ) )
        = ( k2_tarski @ X58 @ X59 ) )
      | ( X58 = X59 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('86',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','55'])).

thf('89',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('90',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['86'])).

thf('91',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('92',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','87','88','89','90','91'])).

thf('93',plain,(
    $false ),
    inference(simplify,[status(thm)],['92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.d9ziASn387
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.68/1.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.68/1.88  % Solved by: fo/fo7.sh
% 1.68/1.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.88  % done 1796 iterations in 1.414s
% 1.68/1.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.68/1.88  % SZS output start Refutation
% 1.68/1.88  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.68/1.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.68/1.88  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.88  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.68/1.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.68/1.88  thf(sk_B_type, type, sk_B: $i).
% 1.68/1.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.68/1.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.68/1.88  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.68/1.88  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.68/1.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.68/1.88  thf(t32_zfmisc_1, conjecture,
% 1.68/1.88    (![A:$i,B:$i]:
% 1.68/1.88     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.68/1.88       ( k2_tarski @ A @ B ) ))).
% 1.68/1.88  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.88    (~( ![A:$i,B:$i]:
% 1.68/1.88        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 1.68/1.88          ( k2_tarski @ A @ B ) ) )),
% 1.68/1.88    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 1.68/1.88  thf('0', plain,
% 1.68/1.88      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 1.68/1.88         != (k2_tarski @ sk_A @ sk_B))),
% 1.68/1.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.88  thf(l51_zfmisc_1, axiom,
% 1.68/1.88    (![A:$i,B:$i]:
% 1.68/1.88     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.68/1.88  thf('1', plain,
% 1.68/1.88      (![X56 : $i, X57 : $i]:
% 1.68/1.88         ((k3_tarski @ (k2_tarski @ X56 @ X57)) = (k2_xboole_0 @ X56 @ X57))),
% 1.68/1.88      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.68/1.88  thf('2', plain,
% 1.68/1.88      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.68/1.88         != (k2_tarski @ sk_A @ sk_B))),
% 1.68/1.88      inference('demod', [status(thm)], ['0', '1'])).
% 1.68/1.88  thf(t29_zfmisc_1, axiom,
% 1.68/1.88    (![A:$i,B:$i]:
% 1.68/1.88     ( ( ( A ) != ( B ) ) =>
% 1.68/1.88       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.68/1.88         ( k2_tarski @ A @ B ) ) ))).
% 1.68/1.88  thf('3', plain,
% 1.68/1.88      (![X58 : $i, X59 : $i]:
% 1.68/1.88         (((k5_xboole_0 @ (k1_tarski @ X58) @ (k1_tarski @ X59))
% 1.68/1.88            = (k2_tarski @ X58 @ X59))
% 1.68/1.88          | ((X58) = (X59)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.68/1.88  thf(t92_xboole_1, axiom,
% 1.68/1.88    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.68/1.88  thf('4', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.68/1.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.68/1.88  thf(t91_xboole_1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.68/1.88       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.68/1.88  thf('5', plain,
% 1.68/1.88      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ X10)
% 1.68/1.88           = (k5_xboole_0 @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.68/1.88  thf('6', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.68/1.88           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['4', '5'])).
% 1.68/1.88  thf(commutativity_k5_xboole_0, axiom,
% 1.68/1.88    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.68/1.88  thf('7', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf(t5_boole, axiom,
% 1.68/1.88    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.68/1.88  thf('8', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 1.68/1.88      inference('cnf', [status(esa)], [t5_boole])).
% 1.68/1.88  thf('9', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['7', '8'])).
% 1.68/1.88  thf('10', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['6', '9'])).
% 1.68/1.88  thf('11', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k1_tarski @ X0)
% 1.68/1.88            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0)))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['3', '10'])).
% 1.68/1.88  thf('12', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('13', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.68/1.88            = (k1_tarski @ X0))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['11', '12'])).
% 1.68/1.88  thf(t70_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.68/1.88  thf('14', plain,
% 1.68/1.88      (![X27 : $i, X28 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf(d1_enumset1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.68/1.88       ( ![E:$i]:
% 1.68/1.88         ( ( r2_hidden @ E @ D ) <=>
% 1.68/1.88           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.68/1.88  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.68/1.88  thf(zf_stmt_2, axiom,
% 1.68/1.88    (![E:$i,C:$i,B:$i,A:$i]:
% 1.68/1.88     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.68/1.88       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.68/1.88  thf(zf_stmt_3, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.88     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.68/1.88       ( ![E:$i]:
% 1.68/1.88         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.68/1.88  thf('15', plain,
% 1.68/1.88      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.68/1.88         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 1.68/1.88          | (r2_hidden @ X19 @ X23)
% 1.68/1.88          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 1.68/1.88      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.68/1.88  thf('16', plain,
% 1.68/1.88      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 1.68/1.88          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 1.68/1.88      inference('simplify', [status(thm)], ['15'])).
% 1.68/1.88  thf('17', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.68/1.88          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.68/1.88      inference('sup+', [status(thm)], ['14', '16'])).
% 1.68/1.88  thf('18', plain,
% 1.68/1.88      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 1.68/1.88         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 1.68/1.88      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.68/1.88  thf('19', plain,
% 1.68/1.88      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.68/1.88         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 1.68/1.88      inference('simplify', [status(thm)], ['18'])).
% 1.68/1.88  thf('20', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.68/1.88      inference('sup-', [status(thm)], ['17', '19'])).
% 1.68/1.88  thf(l31_zfmisc_1, axiom,
% 1.68/1.88    (![A:$i,B:$i]:
% 1.68/1.88     ( ( r2_hidden @ A @ B ) =>
% 1.68/1.88       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 1.68/1.88  thf('21', plain,
% 1.68/1.88      (![X54 : $i, X55 : $i]:
% 1.68/1.88         (((k3_xboole_0 @ X55 @ (k1_tarski @ X54)) = (k1_tarski @ X54))
% 1.68/1.88          | ~ (r2_hidden @ X54 @ X55))),
% 1.68/1.88      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.68/1.88  thf('22', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.68/1.88           = (k1_tarski @ X1))),
% 1.68/1.88      inference('sup-', [status(thm)], ['20', '21'])).
% 1.68/1.88  thf('23', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.68/1.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.68/1.88  thf(t94_xboole_1, axiom,
% 1.68/1.88    (![A:$i,B:$i]:
% 1.68/1.88     ( ( k2_xboole_0 @ A @ B ) =
% 1.68/1.88       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.68/1.88  thf('24', plain,
% 1.68/1.88      (![X12 : $i, X13 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X12 @ X13)
% 1.68/1.88           = (k5_xboole_0 @ (k5_xboole_0 @ X12 @ X13) @ 
% 1.68/1.88              (k3_xboole_0 @ X12 @ X13)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.68/1.88  thf('25', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('26', plain,
% 1.68/1.88      (![X12 : $i, X13 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X12 @ X13)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 1.68/1.88              (k5_xboole_0 @ X12 @ X13)))),
% 1.68/1.88      inference('demod', [status(thm)], ['24', '25'])).
% 1.68/1.88  thf('27', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X0 @ X0)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X0) @ k1_xboole_0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['23', '26'])).
% 1.68/1.88  thf('28', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['7', '8'])).
% 1.68/1.88  thf('30', plain,
% 1.68/1.88      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.68/1.88      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.68/1.88  thf(t112_xboole_1, axiom,
% 1.68/1.88    (![A:$i,B:$i,C:$i]:
% 1.68/1.88     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.68/1.88       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.68/1.88  thf('31', plain,
% 1.68/1.88      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 1.68/1.88           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 1.68/1.88      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.68/1.88  thf('32', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('33', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))
% 1.68/1.88           = (k3_xboole_0 @ (k5_xboole_0 @ X2 @ X1) @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['31', '32'])).
% 1.68/1.88  thf('34', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.68/1.88           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['30', '33'])).
% 1.68/1.88  thf(commutativity_k3_xboole_0, axiom,
% 1.68/1.88    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.68/1.88  thf('35', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.88  thf('36', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.68/1.88           = (k3_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['34', '35'])).
% 1.68/1.88  thf('37', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) @ 
% 1.68/1.88           (k1_tarski @ X0))
% 1.68/1.88           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 1.68/1.88              (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 1.68/1.88      inference('sup+', [status(thm)], ['22', '36'])).
% 1.68/1.88  thf(t69_enumset1, axiom,
% 1.68/1.88    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.68/1.88  thf('38', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('39', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('40', plain,
% 1.68/1.88      (![X27 : $i, X28 : $i]:
% 1.68/1.88         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 1.68/1.88      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.68/1.88  thf('41', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('42', plain,
% 1.68/1.88      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['40', '41'])).
% 1.68/1.88  thf('43', plain,
% 1.68/1.88      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.68/1.88         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 1.68/1.88          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 1.68/1.88      inference('simplify', [status(thm)], ['15'])).
% 1.68/1.88  thf('44', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.68/1.88          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['42', '43'])).
% 1.68/1.88  thf('45', plain,
% 1.68/1.88      (![X14 : $i, X16 : $i, X17 : $i]:
% 1.68/1.88         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 1.68/1.88      inference('simplify', [status(thm)], ['18'])).
% 1.68/1.88  thf('46', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.68/1.88      inference('sup-', [status(thm)], ['44', '45'])).
% 1.68/1.88  thf('47', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['39', '46'])).
% 1.68/1.88  thf('48', plain,
% 1.68/1.88      (![X54 : $i, X55 : $i]:
% 1.68/1.88         (((k3_xboole_0 @ X55 @ (k1_tarski @ X54)) = (k1_tarski @ X54))
% 1.68/1.88          | ~ (r2_hidden @ X54 @ X55))),
% 1.68/1.88      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.68/1.88  thf('49', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k1_tarski @ X0))),
% 1.68/1.88      inference('sup-', [status(thm)], ['47', '48'])).
% 1.68/1.88  thf('50', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('51', plain,
% 1.68/1.88      (![X12 : $i, X13 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X12 @ X13)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 1.68/1.88              (k5_xboole_0 @ X12 @ X13)))),
% 1.68/1.88      inference('demod', [status(thm)], ['24', '25'])).
% 1.68/1.88  thf('52', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X0 @ X1)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['50', '51'])).
% 1.68/1.88  thf('53', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k5_xboole_0 @ (k1_tarski @ X0) @ 
% 1.68/1.88              (k5_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))))),
% 1.68/1.88      inference('sup+', [status(thm)], ['49', '52'])).
% 1.68/1.88  thf('54', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['6', '9'])).
% 1.68/1.88  thf('55', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('demod', [status(thm)], ['53', '54'])).
% 1.68/1.88  thf('56', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['38', '55'])).
% 1.68/1.88  thf('57', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('58', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('demod', [status(thm)], ['53', '54'])).
% 1.68/1.88  thf('59', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))
% 1.68/1.88           = (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['57', '58'])).
% 1.68/1.88  thf('60', plain,
% 1.68/1.88      (![X12 : $i, X13 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X12 @ X13)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 1.68/1.88              (k5_xboole_0 @ X12 @ X13)))),
% 1.68/1.88      inference('demod', [status(thm)], ['24', '25'])).
% 1.68/1.88  thf('61', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['6', '9'])).
% 1.68/1.88  thf('62', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ X1 @ X0)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['60', '61'])).
% 1.68/1.88  thf('63', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('64', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ X1 @ X0)
% 1.68/1.88           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['62', '63'])).
% 1.68/1.88  thf('65', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))
% 1.68/1.88           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 1.68/1.88              (k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0))))),
% 1.68/1.88      inference('sup+', [status(thm)], ['59', '64'])).
% 1.68/1.88  thf('66', plain, (![X11 : $i]: ((k5_xboole_0 @ X11 @ X11) = (k1_xboole_0))),
% 1.68/1.88      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.68/1.88  thf('67', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('68', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k3_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 1.68/1.88           = (k1_tarski @ X1))),
% 1.68/1.88      inference('sup-', [status(thm)], ['20', '21'])).
% 1.68/1.88  thf('69', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.68/1.88  thf('70', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 1.68/1.88           = (k1_tarski @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['68', '69'])).
% 1.68/1.88  thf('71', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k3_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X1))
% 1.68/1.88           = (k1_tarski @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['67', '70'])).
% 1.68/1.88  thf('72', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k1_xboole_0)
% 1.68/1.88           = (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['65', '66', '71'])).
% 1.68/1.88  thf('73', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         ((k1_xboole_0)
% 1.68/1.88           = (k3_xboole_0 @ (k1_tarski @ X0) @ 
% 1.68/1.88              (k5_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X0))))),
% 1.68/1.88      inference('demod', [status(thm)], ['37', '56', '72'])).
% 1.68/1.88  thf('74', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['13', '73'])).
% 1.68/1.88  thf('75', plain,
% 1.68/1.88      (![X58 : $i, X59 : $i]:
% 1.68/1.88         (((k5_xboole_0 @ (k1_tarski @ X58) @ (k1_tarski @ X59))
% 1.68/1.88            = (k2_tarski @ X58 @ X59))
% 1.68/1.88          | ((X58) = (X59)))),
% 1.68/1.88      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 1.68/1.88  thf('76', plain,
% 1.68/1.88      (![X12 : $i, X13 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ X12 @ X13)
% 1.68/1.88           = (k5_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ 
% 1.68/1.88              (k5_xboole_0 @ X12 @ X13)))),
% 1.68/1.88      inference('demod', [status(thm)], ['24', '25'])).
% 1.68/1.88  thf('77', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.68/1.88            = (k5_xboole_0 @ 
% 1.68/1.88               (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 1.68/1.88               (k2_tarski @ X1 @ X0)))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['75', '76'])).
% 1.68/1.88  thf('78', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('79', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.68/1.88            = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ 
% 1.68/1.88               (k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['77', '78'])).
% 1.68/1.88  thf('80', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.68/1.88            = (k5_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0))
% 1.68/1.88          | ((X1) = (X0))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('sup+', [status(thm)], ['74', '79'])).
% 1.68/1.88  thf('81', plain,
% 1.68/1.88      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.68/1.88      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.68/1.88  thf('82', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['7', '8'])).
% 1.68/1.88  thf('83', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.68/1.88            = (k2_tarski @ X1 @ X0))
% 1.68/1.88          | ((X1) = (X0))
% 1.68/1.88          | ((X1) = (X0)))),
% 1.68/1.88      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.68/1.88  thf('84', plain,
% 1.68/1.88      (![X0 : $i, X1 : $i]:
% 1.68/1.88         (((X1) = (X0))
% 1.68/1.88          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 1.68/1.88              = (k2_tarski @ X1 @ X0)))),
% 1.68/1.88      inference('simplify', [status(thm)], ['83'])).
% 1.68/1.88  thf('85', plain,
% 1.68/1.88      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.68/1.88         != (k2_tarski @ sk_A @ sk_B))),
% 1.68/1.88      inference('demod', [status(thm)], ['0', '1'])).
% 1.68/1.88  thf('86', plain,
% 1.68/1.88      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.68/1.88        | ((sk_A) = (sk_B)))),
% 1.68/1.88      inference('sup-', [status(thm)], ['84', '85'])).
% 1.68/1.88  thf('87', plain, (((sk_A) = (sk_B))),
% 1.68/1.88      inference('simplify', [status(thm)], ['86'])).
% 1.68/1.88  thf('88', plain,
% 1.68/1.88      (![X0 : $i]:
% 1.68/1.88         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 1.68/1.88           = (k2_tarski @ X0 @ X0))),
% 1.68/1.88      inference('sup+', [status(thm)], ['38', '55'])).
% 1.68/1.88  thf('89', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('90', plain, (((sk_A) = (sk_B))),
% 1.68/1.88      inference('simplify', [status(thm)], ['86'])).
% 1.68/1.88  thf('91', plain,
% 1.68/1.88      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.68/1.88      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.68/1.88  thf('92', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 1.68/1.88      inference('demod', [status(thm)], ['2', '87', '88', '89', '90', '91'])).
% 1.68/1.88  thf('93', plain, ($false), inference('simplify', [status(thm)], ['92'])).
% 1.68/1.88  
% 1.68/1.88  % SZS output end Refutation
% 1.68/1.88  
% 1.68/1.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
