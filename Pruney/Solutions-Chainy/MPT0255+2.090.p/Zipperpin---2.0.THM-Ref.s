%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DBT9rfh5Ot

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:07 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 256 expanded)
%              Number of leaves         :   32 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  629 (1895 expanded)
%              Number of equality atoms :   63 ( 222 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
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
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
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
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
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
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('34',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('36',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X33 )
      | ( X33
       != ( k1_enumset1 @ X32 @ X31 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('37',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X29 @ ( k1_enumset1 @ X32 @ X31 @ X30 ) )
      | ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X24 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X14: $i] :
      ( r1_tarski @ k1_xboole_0 @ X14 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','58'])).

thf('60',plain,(
    $false ),
    inference('sup-',[status(thm)],['34','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DBT9rfh5Ot
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.71  % Solved by: fo/fo7.sh
% 0.54/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.71  % done 763 iterations in 0.251s
% 0.54/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.71  % SZS output start Refutation
% 0.54/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.54/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.71  thf(t50_zfmisc_1, conjecture,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.54/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.71        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.54/0.71    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.54/0.71  thf('0', plain,
% 0.54/0.71      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.71  thf('1', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf(t94_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k2_xboole_0 @ A @ B ) =
% 0.54/0.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('2', plain,
% 0.54/0.71      (![X22 : $i, X23 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.71           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 0.54/0.71              (k3_xboole_0 @ X22 @ X23)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t94_xboole_1])).
% 0.54/0.71  thf(t91_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i]:
% 0.54/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.54/0.71  thf('3', plain,
% 0.54/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('4', plain,
% 0.54/0.71      (![X22 : $i, X23 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X22 @ X23)
% 0.54/0.71           = (k5_xboole_0 @ X22 @ 
% 0.54/0.71              (k5_xboole_0 @ X23 @ (k3_xboole_0 @ X22 @ X23))))),
% 0.54/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.54/0.71  thf('5', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.54/0.71      inference('sup+', [status(thm)], ['1', '4'])).
% 0.54/0.71  thf(t100_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.54/0.71  thf('6', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('7', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k2_xboole_0 @ X0 @ X1)
% 0.54/0.71           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.71  thf(t92_xboole_1, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.54/0.71  thf('8', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 0.54/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.54/0.71  thf('9', plain,
% 0.54/0.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 0.54/0.71           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.54/0.71  thf('10', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.54/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.54/0.71  thf('11', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf(t5_boole, axiom,
% 0.54/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.71  thf('12', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.54/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.71  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.54/0.71  thf('14', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('demod', [status(thm)], ['10', '13'])).
% 0.54/0.71  thf('15', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X0 @ X1)
% 0.54/0.71           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['7', '14'])).
% 0.54/0.71  thf('16', plain,
% 0.54/0.71      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['0', '15'])).
% 0.54/0.71  thf('17', plain,
% 0.54/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.54/0.71  thf('18', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.54/0.71  thf('19', plain,
% 0.54/0.71      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.54/0.71  thf(t36_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.71  thf('20', plain,
% 0.54/0.71      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.54/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.71  thf(t28_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.71  thf('21', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.54/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.71  thf('22', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.54/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.71  thf('23', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('24', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.54/0.71           = (k4_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.54/0.71  thf('25', plain,
% 0.54/0.71      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['19', '24'])).
% 0.54/0.71  thf('26', plain,
% 0.54/0.71      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.54/0.71  thf('27', plain,
% 0.54/0.71      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.71  thf('28', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf(l97_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.54/0.71  thf('29', plain,
% 0.54/0.71      (![X8 : $i, X9 : $i]:
% 0.54/0.71         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.54/0.71      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.54/0.71  thf('30', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.54/0.71          (k4_xboole_0 @ X1 @ X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['28', '29'])).
% 0.54/0.71  thf('31', plain,
% 0.54/0.71      ((r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) @ 
% 0.54/0.71        (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.54/0.71      inference('sup+', [status(thm)], ['27', '30'])).
% 0.54/0.71  thf('32', plain,
% 0.54/0.71      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.54/0.71  thf('33', plain,
% 0.54/0.71      (((k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.54/0.71         = (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.54/0.71  thf('34', plain,
% 0.54/0.71      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_A @ sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.54/0.71  thf(t70_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.71  thf('35', plain,
% 0.54/0.71      (![X36 : $i, X37 : $i]:
% 0.54/0.71         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.54/0.71      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.71  thf(d1_enumset1, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.71       ( ![E:$i]:
% 0.54/0.71         ( ( r2_hidden @ E @ D ) <=>
% 0.54/0.71           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.54/0.71  thf(zf_stmt_2, axiom,
% 0.54/0.71    (![E:$i,C:$i,B:$i,A:$i]:
% 0.54/0.71     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.54/0.71       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.54/0.71  thf(zf_stmt_3, axiom,
% 0.54/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.71     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.71       ( ![E:$i]:
% 0.54/0.71         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.54/0.71  thf('36', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.71         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 0.54/0.71          | (r2_hidden @ X29 @ X33)
% 0.54/0.71          | ((X33) != (k1_enumset1 @ X32 @ X31 @ X30)))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.71  thf('37', plain,
% 0.54/0.71      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.54/0.71         ((r2_hidden @ X29 @ (k1_enumset1 @ X32 @ X31 @ X30))
% 0.54/0.71          | (zip_tseitin_0 @ X29 @ X30 @ X31 @ X32))),
% 0.54/0.71      inference('simplify', [status(thm)], ['36'])).
% 0.54/0.71  thf('38', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.54/0.71          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['35', '37'])).
% 0.54/0.71  thf('39', plain,
% 0.54/0.71      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.54/0.71         (((X25) != (X24)) | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X24))),
% 0.54/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.71  thf('40', plain,
% 0.54/0.71      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.54/0.71         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X24)),
% 0.54/0.71      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.71  thf('41', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['38', '40'])).
% 0.54/0.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.71  thf('42', plain, (![X14 : $i]: (r1_tarski @ k1_xboole_0 @ X14)),
% 0.54/0.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.71  thf('43', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.54/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.71  thf('44', plain,
% 0.54/0.71      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.71  thf('45', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf('46', plain,
% 0.54/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['44', '45'])).
% 0.54/0.71  thf('47', plain,
% 0.54/0.71      (![X10 : $i, X11 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X10 @ X11)
% 0.54/0.71           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.54/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.54/0.71  thf('48', plain,
% 0.54/0.71      (![X0 : $i]:
% 0.54/0.71         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['46', '47'])).
% 0.54/0.71  thf('49', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.54/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.54/0.71  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.71      inference('sup+', [status(thm)], ['48', '49'])).
% 0.54/0.71  thf('51', plain,
% 0.54/0.71      (![X15 : $i, X16 : $i]: (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X15)),
% 0.54/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.54/0.71  thf('52', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.71      inference('sup+', [status(thm)], ['50', '51'])).
% 0.54/0.71  thf('53', plain,
% 0.54/0.71      (![X12 : $i, X13 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.54/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.71  thf('54', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['52', '53'])).
% 0.54/0.71  thf('55', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.71  thf(t4_xboole_0, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.54/0.71  thf('56', plain,
% 0.54/0.71      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.54/0.71         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.54/0.71          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.54/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.54/0.71  thf('57', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.71      inference('sup-', [status(thm)], ['55', '56'])).
% 0.54/0.71  thf('58', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['54', '57'])).
% 0.54/0.71  thf('59', plain,
% 0.54/0.71      (![X0 : $i, X1 : $i]:
% 0.54/0.71         ~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.54/0.71      inference('sup-', [status(thm)], ['41', '58'])).
% 0.54/0.71  thf('60', plain, ($false), inference('sup-', [status(thm)], ['34', '59'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
