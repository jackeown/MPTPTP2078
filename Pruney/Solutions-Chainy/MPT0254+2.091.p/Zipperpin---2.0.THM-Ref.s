%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l2ExxZ8IK3

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:47 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 252 expanded)
%              Number of leaves         :   31 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  599 (1832 expanded)
%              Number of equality atoms :   66 ( 227 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k5_xboole_0 @ X16 @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('30',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('31',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','56'])).

thf('58',plain,(
    $false ),
    inference('sup-',[status(thm)],['30','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l2ExxZ8IK3
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 12:04:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.48/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.67  % Solved by: fo/fo7.sh
% 0.48/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.67  % done 705 iterations in 0.258s
% 0.48/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.67  % SZS output start Refutation
% 0.48/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.67  thf(t49_zfmisc_1, conjecture,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.48/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.67    (~( ![A:$i,B:$i]:
% 0.48/0.67        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.48/0.67    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.48/0.67  thf('0', plain,
% 0.48/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.67  thf('1', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.67  thf(t94_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k2_xboole_0 @ A @ B ) =
% 0.48/0.67       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.67  thf('2', plain,
% 0.48/0.67      (![X20 : $i, X21 : $i]:
% 0.48/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.48/0.67           = (k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ 
% 0.48/0.67              (k3_xboole_0 @ X20 @ X21)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.48/0.67  thf(t91_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.48/0.67       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.48/0.67  thf('3', plain,
% 0.48/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.48/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.67  thf('4', plain,
% 0.48/0.67      (![X20 : $i, X21 : $i]:
% 0.48/0.67         ((k2_xboole_0 @ X20 @ X21)
% 0.48/0.67           = (k5_xboole_0 @ X20 @ 
% 0.48/0.67              (k5_xboole_0 @ X21 @ (k3_xboole_0 @ X20 @ X21))))),
% 0.48/0.67      inference('demod', [status(thm)], ['2', '3'])).
% 0.48/0.67  thf('5', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.67           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.48/0.67      inference('sup+', [status(thm)], ['1', '4'])).
% 0.48/0.67  thf(t100_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.67  thf('6', plain,
% 0.48/0.67      (![X10 : $i, X11 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X10 @ X11)
% 0.48/0.67           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.67  thf('7', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k2_xboole_0 @ X0 @ X1)
% 0.48/0.67           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('demod', [status(thm)], ['5', '6'])).
% 0.48/0.67  thf(t92_xboole_1, axiom,
% 0.48/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.67  thf('8', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ X19) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.48/0.67  thf('9', plain,
% 0.48/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ (k5_xboole_0 @ X16 @ X17) @ X18)
% 0.48/0.67           = (k5_xboole_0 @ X16 @ (k5_xboole_0 @ X17 @ X18)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.48/0.67  thf('10', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.48/0.67           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf(commutativity_k5_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.48/0.67  thf('11', plain,
% 0.48/0.67      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.67      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.67  thf(t5_boole, axiom,
% 0.48/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.67  thf('12', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.67  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('14', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('demod', [status(thm)], ['10', '13'])).
% 0.48/0.67  thf('15', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.67           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['7', '14'])).
% 0.48/0.67  thf('16', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.48/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['0', '15'])).
% 0.48/0.67  thf('17', plain,
% 0.48/0.67      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.48/0.67      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.48/0.67  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.67  thf('19', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.48/0.67  thf(t48_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.67  thf('20', plain,
% 0.48/0.67      (![X13 : $i, X14 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.48/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.67  thf('21', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.48/0.67         = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['19', '20'])).
% 0.48/0.67  thf('22', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.48/0.67  thf('23', plain,
% 0.48/0.67      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.48/0.67  thf('24', plain,
% 0.48/0.67      (![X10 : $i, X11 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X10 @ X11)
% 0.48/0.67           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.67  thf(l97_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.48/0.67  thf('25', plain,
% 0.48/0.67      (![X8 : $i, X9 : $i]:
% 0.48/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.48/0.67      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.48/0.67  thf('26', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.48/0.67          (k4_xboole_0 @ X1 @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.67  thf('27', plain,
% 0.48/0.67      ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.48/0.67        (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['23', '26'])).
% 0.48/0.67  thf('28', plain,
% 0.48/0.67      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.48/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.48/0.67  thf('29', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.48/0.67  thf('30', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))),
% 0.48/0.67      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.48/0.67  thf(t69_enumset1, axiom,
% 0.48/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.67  thf('31', plain,
% 0.48/0.67      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.48/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.67  thf(t70_enumset1, axiom,
% 0.48/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.67  thf('32', plain,
% 0.48/0.67      (![X35 : $i, X36 : $i]:
% 0.48/0.67         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.48/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.67  thf(d1_enumset1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.67       ( ![E:$i]:
% 0.48/0.67         ( ( r2_hidden @ E @ D ) <=>
% 0.48/0.67           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.67  thf(zf_stmt_2, axiom,
% 0.48/0.67    (![E:$i,C:$i,B:$i,A:$i]:
% 0.48/0.67     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.48/0.67       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.48/0.67  thf(zf_stmt_3, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.67       ( ![E:$i]:
% 0.48/0.67         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.48/0.67  thf('33', plain,
% 0.48/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.48/0.67         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.48/0.67          | (r2_hidden @ X27 @ X31)
% 0.48/0.67          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.67  thf('34', plain,
% 0.48/0.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.48/0.67         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.48/0.67          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.48/0.67      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.67  thf('35', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.67         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.48/0.67          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.48/0.67      inference('sup+', [status(thm)], ['32', '34'])).
% 0.48/0.67  thf('36', plain,
% 0.48/0.67      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.48/0.67         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.67  thf('37', plain,
% 0.48/0.67      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.48/0.67         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.48/0.67      inference('simplify', [status(thm)], ['36'])).
% 0.48/0.67  thf('38', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.48/0.67      inference('sup-', [status(thm)], ['35', '37'])).
% 0.48/0.67  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['31', '38'])).
% 0.48/0.67  thf(t2_boole, axiom,
% 0.48/0.67    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.48/0.67  thf('40', plain,
% 0.48/0.67      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.67  thf('41', plain,
% 0.48/0.67      (![X10 : $i, X11 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X10 @ X11)
% 0.48/0.67           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.67  thf('42', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.67  thf('43', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.67  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['42', '43'])).
% 0.48/0.67  thf('45', plain,
% 0.48/0.67      (![X13 : $i, X14 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.48/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.67  thf('46', plain,
% 0.48/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['44', '45'])).
% 0.48/0.67  thf('47', plain,
% 0.48/0.67      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [t2_boole])).
% 0.48/0.67  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.67      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.67  thf('49', plain,
% 0.48/0.67      (![X13 : $i, X14 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.67           = (k3_xboole_0 @ X13 @ X14))),
% 0.48/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.67  thf('50', plain,
% 0.48/0.67      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['48', '49'])).
% 0.48/0.67  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['42', '43'])).
% 0.48/0.67  thf('52', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.48/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.48/0.67  thf('53', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.48/0.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.67  thf(t4_xboole_0, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.67            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.67  thf('54', plain,
% 0.48/0.67      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.48/0.67          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.48/0.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.67  thf('55', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.67          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.67  thf('56', plain,
% 0.48/0.67      (![X0 : $i, X1 : $i]:
% 0.48/0.67         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['52', '55'])).
% 0.48/0.67  thf('57', plain,
% 0.48/0.67      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['39', '56'])).
% 0.48/0.67  thf('58', plain, ($false), inference('sup-', [status(thm)], ['30', '57'])).
% 0.48/0.67  
% 0.48/0.67  % SZS output end Refutation
% 0.48/0.67  
% 0.48/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
