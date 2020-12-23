%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UWUCWBkQnx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:44 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 168 expanded)
%              Number of leaves         :   30 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  727 (1313 expanded)
%              Number of equality atoms :   62 ( 134 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X24 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('14',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('28',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X21 @ X20 )
      = ( k2_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','39'])).

thf('41',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('42',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('50',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['41','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf('63',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['40','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UWUCWBkQnx
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.65/1.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.89  % Solved by: fo/fo7.sh
% 1.65/1.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.89  % done 1637 iterations in 1.443s
% 1.65/1.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.89  % SZS output start Refutation
% 1.65/1.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.65/1.89  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.65/1.89  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.65/1.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.65/1.89  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.65/1.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.65/1.89  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.65/1.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.65/1.89  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.65/1.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.65/1.89  thf(t63_zfmisc_1, conjecture,
% 1.65/1.89    (![A:$i,B:$i,C:$i]:
% 1.65/1.89     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.65/1.89       ( r2_hidden @ A @ C ) ))).
% 1.65/1.89  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.89    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.89        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.65/1.89          ( r2_hidden @ A @ C ) ) )),
% 1.65/1.89    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 1.65/1.89  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(t70_enumset1, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.65/1.89  thf('1', plain,
% 1.65/1.89      (![X34 : $i, X35 : $i]:
% 1.65/1.89         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.65/1.89      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.65/1.89  thf(d1_enumset1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.65/1.89       ( ![E:$i]:
% 1.65/1.89         ( ( r2_hidden @ E @ D ) <=>
% 1.65/1.89           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.65/1.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.65/1.89  thf(zf_stmt_2, axiom,
% 1.65/1.89    (![E:$i,C:$i,B:$i,A:$i]:
% 1.65/1.89     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.65/1.89       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.65/1.89  thf(zf_stmt_3, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.89     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.65/1.89       ( ![E:$i]:
% 1.65/1.89         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.65/1.89  thf('2', plain,
% 1.65/1.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.65/1.89         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 1.65/1.89          | (r2_hidden @ X27 @ X31)
% 1.65/1.89          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.65/1.89  thf('3', plain,
% 1.65/1.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.89         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 1.65/1.89          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 1.65/1.89      inference('simplify', [status(thm)], ['2'])).
% 1.65/1.89  thf('4', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.65/1.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['1', '3'])).
% 1.65/1.89  thf('5', plain,
% 1.65/1.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.65/1.89         (((X23) != (X24)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.89  thf('6', plain,
% 1.65/1.89      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.65/1.89         ~ (zip_tseitin_0 @ X24 @ X24 @ X25 @ X22)),
% 1.65/1.89      inference('simplify', [status(thm)], ['5'])).
% 1.65/1.89  thf('7', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.65/1.89      inference('sup-', [status(thm)], ['4', '6'])).
% 1.65/1.89  thf('8', plain,
% 1.65/1.89      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.65/1.89         = (k2_tarski @ sk_A @ sk_B))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.89  thf(commutativity_k2_tarski, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.65/1.89  thf('9', plain,
% 1.65/1.89      (![X20 : $i, X21 : $i]:
% 1.65/1.89         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.65/1.89  thf('10', plain,
% 1.65/1.89      (![X20 : $i, X21 : $i]:
% 1.65/1.89         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.65/1.89  thf('11', plain,
% 1.65/1.89      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.65/1.89         = (k2_tarski @ sk_B @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.65/1.89  thf(t95_xboole_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( k3_xboole_0 @ A @ B ) =
% 1.65/1.89       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.65/1.89  thf('12', plain,
% 1.65/1.89      (![X18 : $i, X19 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ X18 @ X19)
% 1.65/1.89           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.65/1.89              (k2_xboole_0 @ X18 @ X19)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.65/1.89  thf(commutativity_k5_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.65/1.89  thf('13', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.89  thf('14', plain,
% 1.65/1.89      (![X18 : $i, X19 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ X18 @ X19)
% 1.65/1.89           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.65/1.89              (k5_xboole_0 @ X18 @ X19)))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf(t1_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i]:
% 1.65/1.89     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.65/1.89       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.65/1.89  thf('15', plain,
% 1.65/1.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.65/1.89         ((r2_hidden @ X4 @ X5)
% 1.65/1.89          | (r2_hidden @ X4 @ X6)
% 1.65/1.89          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.65/1.89  thf('16', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.65/1.89          | (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 1.65/1.89          | (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['14', '15'])).
% 1.65/1.89  thf('17', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 1.65/1.89          | (r2_hidden @ X0 @ 
% 1.65/1.89             (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))
% 1.65/1.89          | (r2_hidden @ X0 @ 
% 1.65/1.89             (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['11', '16'])).
% 1.65/1.89  thf('18', plain,
% 1.65/1.89      (![X20 : $i, X21 : $i]:
% 1.65/1.89         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.65/1.89  thf(l51_zfmisc_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.65/1.89  thf('19', plain,
% 1.65/1.89      (![X61 : $i, X62 : $i]:
% 1.65/1.89         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.65/1.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.65/1.89  thf('20', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['18', '19'])).
% 1.65/1.89  thf('21', plain,
% 1.65/1.89      (![X61 : $i, X62 : $i]:
% 1.65/1.89         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.65/1.89      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.65/1.89  thf('22', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['20', '21'])).
% 1.65/1.89  thf('23', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.89  thf('24', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 1.65/1.89          | (r2_hidden @ X0 @ 
% 1.65/1.89             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 1.65/1.89          | (r2_hidden @ X0 @ 
% 1.65/1.89             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.65/1.89      inference('demod', [status(thm)], ['17', '22', '23'])).
% 1.65/1.89  thf('25', plain,
% 1.65/1.89      (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 1.65/1.89        | (r2_hidden @ sk_A @ 
% 1.65/1.89           (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.65/1.89      inference('sup-', [status(thm)], ['7', '24'])).
% 1.65/1.89  thf('26', plain,
% 1.65/1.89      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.65/1.89         = (k2_tarski @ sk_B @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.65/1.89  thf(l97_xboole_1, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.65/1.89  thf('27', plain,
% 1.65/1.89      (![X12 : $i, X13 : $i]:
% 1.65/1.89         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 1.65/1.89      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.65/1.89  thf('28', plain,
% 1.65/1.89      ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 1.65/1.89        (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['26', '27'])).
% 1.65/1.89  thf('29', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.89  thf('30', plain,
% 1.65/1.89      ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 1.65/1.89        (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.65/1.89      inference('demod', [status(thm)], ['28', '29'])).
% 1.65/1.89  thf('31', plain,
% 1.65/1.89      (![X20 : $i, X21 : $i]:
% 1.65/1.89         ((k2_tarski @ X21 @ X20) = (k2_tarski @ X20 @ X21))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.65/1.89  thf('32', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.65/1.89          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['1', '3'])).
% 1.65/1.89  thf('33', plain,
% 1.65/1.89      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.65/1.89         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 1.65/1.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.65/1.89  thf('34', plain,
% 1.65/1.89      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.65/1.89         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 1.65/1.89      inference('simplify', [status(thm)], ['33'])).
% 1.65/1.89  thf('35', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.65/1.89      inference('sup-', [status(thm)], ['32', '34'])).
% 1.65/1.89  thf(t3_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]:
% 1.65/1.89     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.65/1.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.65/1.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.65/1.89            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.65/1.89  thf('36', plain,
% 1.65/1.89      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.65/1.89         (~ (r2_hidden @ X10 @ X8)
% 1.65/1.89          | ~ (r2_hidden @ X10 @ X11)
% 1.65/1.89          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.65/1.89      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.65/1.89  thf('37', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.65/1.89          | ~ (r2_hidden @ X1 @ X2))),
% 1.65/1.89      inference('sup-', [status(thm)], ['35', '36'])).
% 1.65/1.89  thf('38', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.89         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.65/1.89          | ~ (r2_hidden @ X0 @ X2))),
% 1.65/1.89      inference('sup-', [status(thm)], ['31', '37'])).
% 1.65/1.89  thf('39', plain,
% 1.65/1.89      (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.65/1.89      inference('sup-', [status(thm)], ['30', '38'])).
% 1.65/1.89  thf('40', plain,
% 1.65/1.89      ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.65/1.89      inference('clc', [status(thm)], ['25', '39'])).
% 1.65/1.89  thf('41', plain,
% 1.65/1.89      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.65/1.89         = (k2_tarski @ sk_B @ sk_A))),
% 1.65/1.89      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.65/1.89  thf('42', plain,
% 1.65/1.89      (![X18 : $i, X19 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ X18 @ X19)
% 1.65/1.89           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.65/1.89              (k5_xboole_0 @ X18 @ X19)))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf('43', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.89  thf(t92_xboole_1, axiom,
% 1.65/1.89    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.65/1.89  thf('44', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.89  thf(t91_xboole_1, axiom,
% 1.65/1.89    (![A:$i,B:$i,C:$i]:
% 1.65/1.89     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.65/1.89       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.65/1.89  thf('45', plain,
% 1.65/1.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.89         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.65/1.89           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.65/1.89  thf('46', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.65/1.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['44', '45'])).
% 1.65/1.89  thf(idempotence_k2_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.65/1.89  thf('47', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.65/1.89      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.65/1.89  thf('48', plain,
% 1.65/1.89      (![X18 : $i, X19 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ X18 @ X19)
% 1.65/1.89           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.65/1.89              (k5_xboole_0 @ X18 @ X19)))),
% 1.65/1.89      inference('demod', [status(thm)], ['12', '13'])).
% 1.65/1.89  thf('49', plain,
% 1.65/1.89      (![X0 : $i]:
% 1.65/1.89         ((k3_xboole_0 @ X0 @ X0)
% 1.65/1.89           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['47', '48'])).
% 1.65/1.89  thf(idempotence_k3_xboole_0, axiom,
% 1.65/1.89    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.65/1.89  thf('50', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.65/1.89      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.65/1.89  thf('51', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.65/1.89      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.65/1.89  thf('52', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.65/1.89      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.65/1.89  thf('53', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.65/1.89  thf('54', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.65/1.89      inference('sup+', [status(thm)], ['52', '53'])).
% 1.65/1.89  thf('55', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('demod', [status(thm)], ['46', '54'])).
% 1.65/1.89  thf('56', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['43', '55'])).
% 1.65/1.89  thf('57', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((k2_xboole_0 @ X1 @ X0)
% 1.65/1.89           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['42', '56'])).
% 1.65/1.89  thf('58', plain,
% 1.65/1.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.65/1.89         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.65/1.89           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.65/1.89      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.65/1.89  thf('59', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((k2_xboole_0 @ X1 @ X0)
% 1.65/1.89           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.65/1.89      inference('demod', [status(thm)], ['57', '58'])).
% 1.65/1.89  thf('60', plain,
% 1.65/1.89      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.65/1.89         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 1.65/1.89            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.65/1.89      inference('sup+', [status(thm)], ['41', '59'])).
% 1.65/1.89  thf('61', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.65/1.89      inference('sup+', [status(thm)], ['20', '21'])).
% 1.65/1.89  thf('62', plain,
% 1.65/1.89      (![X0 : $i, X1 : $i]:
% 1.65/1.89         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.65/1.89      inference('sup+', [status(thm)], ['43', '55'])).
% 1.65/1.89  thf('63', plain,
% 1.65/1.89      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) = (sk_C_1))),
% 1.65/1.89      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.65/1.89  thf('64', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 1.65/1.89      inference('demod', [status(thm)], ['40', '63'])).
% 1.65/1.89  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 1.65/1.89  
% 1.65/1.89  % SZS output end Refutation
% 1.65/1.89  
% 1.65/1.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
