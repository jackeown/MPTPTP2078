%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTbTOqJGLq

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:08 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 127 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  629 ( 839 expanded)
%              Number of equality atoms :   76 ( 105 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('12',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k5_xboole_0 @ sk_C_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','41','48'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('50',plain,(
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

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('59',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('62',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','64'])).

thf('66',plain,(
    $false ),
    inference('sup-',[status(thm)],['57','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JTbTOqJGLq
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:53:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 399 iterations in 0.287s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.56/0.74  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.56/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.56/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.56/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.74  thf(t50_zfmisc_1, conjecture,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.74        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.56/0.74  thf('0', plain,
% 0.56/0.74      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(t94_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k2_xboole_0 @ A @ B ) =
% 0.56/0.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      (![X21 : $i, X22 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X21 @ X22)
% 0.56/0.74           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.56/0.74              (k3_xboole_0 @ X21 @ X22)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.56/0.74  thf(t91_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i]:
% 0.56/0.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.56/0.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.56/0.74           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.74  thf('4', plain,
% 0.56/0.74      (![X21 : $i, X22 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X21 @ X22)
% 0.56/0.74           = (k5_xboole_0 @ X21 @ 
% 0.56/0.74              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.56/0.74      inference('demod', [status(thm)], ['2', '3'])).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.56/0.74           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.74  thf(commutativity_k5_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 0.56/0.74           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.56/0.74  thf('8', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X1 @ X0)
% 0.56/0.74           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['4', '7'])).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf(t100_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.56/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.74  thf('11', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X1 @ X0)
% 0.56/0.74           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.56/0.74  thf(idempotence_k3_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.56/0.74  thf('12', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.56/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.56/0.74  thf('13', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.56/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['12', '13'])).
% 0.56/0.74  thf(t2_boole, axiom,
% 0.56/0.74    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.56/0.74  thf('15', plain,
% 0.56/0.74      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X10 @ X11)
% 0.56/0.74           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['15', '16'])).
% 0.56/0.74  thf(t5_boole, axiom,
% 0.56/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.56/0.74  thf('18', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.74  thf('19', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['17', '18'])).
% 0.56/0.74  thf(t48_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      (![X13 : $i, X14 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.56/0.74           = (k3_xboole_0 @ X13 @ X14))),
% 0.56/0.74      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['19', '20'])).
% 0.56/0.74  thf('22', plain,
% 0.56/0.74      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.56/0.74  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['21', '22'])).
% 0.56/0.74  thf('24', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.56/0.74      inference('demod', [status(thm)], ['14', '23'])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.56/0.74           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.56/0.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['24', '25'])).
% 0.56/0.74  thf('27', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf('28', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.74  thf('29', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('demod', [status(thm)], ['26', '29'])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k4_xboole_0 @ X1 @ X0)
% 0.56/0.74           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['11', '30'])).
% 0.56/0.74  thf('32', plain,
% 0.56/0.74      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.56/0.74         = (k5_xboole_0 @ sk_C_1 @ k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['1', '31'])).
% 0.56/0.74  thf('33', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.56/0.74  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (sk_C_1))),
% 0.56/0.74      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.56/0.74  thf(t79_xboole_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.56/0.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.56/0.74  thf(d7_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.56/0.74       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.74  thf('37', plain,
% 0.56/0.74      (![X2 : $i, X3 : $i]:
% 0.56/0.74         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.56/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.56/0.74  thf('39', plain, (((k3_xboole_0 @ sk_C_1 @ sk_C_1) = (k1_xboole_0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['35', '38'])).
% 0.56/0.74  thf('40', plain, (![X5 : $i]: ((k3_xboole_0 @ X5 @ X5) = (X5))),
% 0.56/0.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.56/0.74  thf('41', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['39', '40'])).
% 0.56/0.74  thf('42', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      (![X21 : $i, X22 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X21 @ X22)
% 0.56/0.74           = (k5_xboole_0 @ X21 @ 
% 0.56/0.74              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 0.56/0.74      inference('demod', [status(thm)], ['2', '3'])).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 0.56/0.74           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.56/0.74      inference('sup+', [status(thm)], ['42', '43'])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['44', '45'])).
% 0.56/0.74  thf('47', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.56/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.56/0.74  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.56/0.74      inference('sup+', [status(thm)], ['46', '47'])).
% 0.56/0.74  thf('49', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['0', '41', '48'])).
% 0.56/0.74  thf(t70_enumset1, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.56/0.74  thf('50', plain,
% 0.56/0.74      (![X35 : $i, X36 : $i]:
% 0.56/0.74         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.56/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.56/0.74  thf(d1_enumset1, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.56/0.74       ( ![E:$i]:
% 0.56/0.74         ( ( r2_hidden @ E @ D ) <=>
% 0.56/0.74           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.56/0.74  thf(zf_stmt_2, axiom,
% 0.56/0.74    (![E:$i,C:$i,B:$i,A:$i]:
% 0.56/0.74     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.56/0.74       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_3, axiom,
% 0.56/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.56/0.74       ( ![E:$i]:
% 0.56/0.74         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.56/0.74         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.56/0.74          | (r2_hidden @ X28 @ X32)
% 0.56/0.74          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.56/0.74  thf('52', plain,
% 0.56/0.74      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.56/0.74         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.56/0.74          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.56/0.74      inference('simplify', [status(thm)], ['51'])).
% 0.56/0.74  thf('53', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.74         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.56/0.74          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.56/0.74      inference('sup+', [status(thm)], ['50', '52'])).
% 0.56/0.74  thf('54', plain,
% 0.56/0.74      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.56/0.74         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.56/0.74  thf('55', plain,
% 0.56/0.74      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.56/0.74         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 0.56/0.74      inference('simplify', [status(thm)], ['54'])).
% 0.56/0.74  thf('56', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.56/0.74      inference('sup-', [status(thm)], ['53', '55'])).
% 0.56/0.74  thf('57', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.56/0.74      inference('sup+', [status(thm)], ['49', '56'])).
% 0.56/0.74  thf('58', plain,
% 0.56/0.74      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.56/0.74  thf(t4_xboole_0, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.56/0.74            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.56/0.74  thf('59', plain,
% 0.56/0.74      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.56/0.74          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.56/0.74      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.56/0.74  thf('60', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['58', '59'])).
% 0.56/0.74  thf('61', plain,
% 0.56/0.74      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_boole])).
% 0.56/0.74  thf('62', plain,
% 0.56/0.74      (![X2 : $i, X4 : $i]:
% 0.56/0.74         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.56/0.74      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.74  thf('63', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['61', '62'])).
% 0.56/0.74  thf('64', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.56/0.74      inference('simplify', [status(thm)], ['63'])).
% 0.56/0.74  thf('65', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.56/0.74      inference('demod', [status(thm)], ['60', '64'])).
% 0.56/0.74  thf('66', plain, ($false), inference('sup-', [status(thm)], ['57', '65'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
