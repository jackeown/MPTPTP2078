%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXKiYkbYyp

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:47 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 352 expanded)
%              Number of leaves         :   32 ( 128 expanded)
%              Depth                    :   13
%              Number of atoms          :  953 (3010 expanded)
%              Number of equality atoms :   82 ( 314 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X22 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X32 @ X33 @ X34 @ X35 )
      = ( k2_xboole_0 @ ( k2_tarski @ X32 @ X33 ) @ ( k2_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_enumset1 @ X1 @ X0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X39 @ X38 @ X37 @ X36 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X1 @ X0 @ X1 )
      = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('34',plain,(
    ! [X44: $i,X45: $i] :
      ( ( k1_enumset1 @ X44 @ X44 @ X45 )
      = ( k2_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k5_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('44',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('49',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

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

thf('55',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','57'])).

thf('59',plain,(
    r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['41','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('63',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('66',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('70',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('72',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('73',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','78'])).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['63','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['65','77'])).

thf('85',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['59','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JXKiYkbYyp
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.28/1.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.28/1.52  % Solved by: fo/fo7.sh
% 1.28/1.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.28/1.52  % done 1465 iterations in 1.072s
% 1.28/1.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.28/1.52  % SZS output start Refutation
% 1.28/1.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.28/1.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.28/1.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.28/1.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.28/1.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.28/1.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.28/1.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.28/1.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.28/1.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.28/1.52  thf(sk_B_type, type, sk_B: $i).
% 1.28/1.52  thf(sk_A_type, type, sk_A: $i).
% 1.28/1.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.28/1.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.28/1.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.28/1.52  thf(t63_zfmisc_1, conjecture,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.28/1.52       ( r2_hidden @ A @ C ) ))).
% 1.28/1.52  thf(zf_stmt_0, negated_conjecture,
% 1.28/1.52    (~( ![A:$i,B:$i,C:$i]:
% 1.28/1.52        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 1.28/1.52          ( r2_hidden @ A @ C ) ) )),
% 1.28/1.52    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 1.28/1.52  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(t70_enumset1, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.28/1.52  thf('1', plain,
% 1.28/1.52      (![X44 : $i, X45 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.28/1.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.28/1.52  thf(d1_enumset1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.28/1.52       ( ![E:$i]:
% 1.28/1.52         ( ( r2_hidden @ E @ D ) <=>
% 1.28/1.52           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.28/1.52  thf(zf_stmt_2, axiom,
% 1.28/1.52    (![E:$i,C:$i,B:$i,A:$i]:
% 1.28/1.52     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.28/1.52       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.28/1.52  thf(zf_stmt_3, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.52     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.28/1.52       ( ![E:$i]:
% 1.28/1.52         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.28/1.52  thf('2', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.28/1.52         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.28/1.52          | (r2_hidden @ X25 @ X29)
% 1.28/1.52          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.28/1.52  thf('3', plain,
% 1.28/1.52      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.28/1.52         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 1.28/1.52          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 1.28/1.52      inference('simplify', [status(thm)], ['2'])).
% 1.28/1.52  thf('4', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.28/1.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['1', '3'])).
% 1.28/1.52  thf('5', plain,
% 1.28/1.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.28/1.52         (((X21) != (X22)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.28/1.52  thf('6', plain,
% 1.28/1.52      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.28/1.52         ~ (zip_tseitin_0 @ X22 @ X22 @ X23 @ X20)),
% 1.28/1.52      inference('simplify', [status(thm)], ['5'])).
% 1.28/1.52  thf('7', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup-', [status(thm)], ['4', '6'])).
% 1.28/1.52  thf('8', plain,
% 1.28/1.52      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.28/1.52         = (k2_tarski @ sk_A @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(t95_xboole_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( k3_xboole_0 @ A @ B ) =
% 1.28/1.52       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.28/1.52  thf('9', plain,
% 1.28/1.52      (![X18 : $i, X19 : $i]:
% 1.28/1.52         ((k3_xboole_0 @ X18 @ X19)
% 1.28/1.52           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 1.28/1.52              (k2_xboole_0 @ X18 @ X19)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.28/1.52  thf(commutativity_k5_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.28/1.52  thf('10', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.52  thf('11', plain,
% 1.28/1.52      (![X18 : $i, X19 : $i]:
% 1.28/1.52         ((k3_xboole_0 @ X18 @ X19)
% 1.28/1.52           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.28/1.52              (k5_xboole_0 @ X18 @ X19)))),
% 1.28/1.52      inference('demod', [status(thm)], ['9', '10'])).
% 1.28/1.52  thf(t1_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.28/1.52       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.28/1.52  thf('12', plain,
% 1.28/1.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.28/1.52         ((r2_hidden @ X4 @ X5)
% 1.28/1.52          | (r2_hidden @ X4 @ X6)
% 1.28/1.52          | ~ (r2_hidden @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.28/1.52  thf('13', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.28/1.52          | (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 1.28/1.52          | (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['11', '12'])).
% 1.28/1.52  thf('14', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['8', '13'])).
% 1.28/1.52  thf('15', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.52  thf('16', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B))))),
% 1.28/1.52      inference('demod', [status(thm)], ['14', '15'])).
% 1.28/1.52  thf(idempotence_k2_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.28/1.52  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.28/1.52  thf(l53_enumset1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.52     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 1.28/1.52       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 1.28/1.52  thf('18', plain,
% 1.28/1.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 1.28/1.52           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k2_tarski @ X34 @ X35)))),
% 1.28/1.52      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.28/1.52  thf('19', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['17', '18'])).
% 1.28/1.52  thf('20', plain,
% 1.28/1.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X32 @ X33 @ X34 @ X35)
% 1.28/1.52           = (k2_xboole_0 @ (k2_tarski @ X32 @ X33) @ (k2_tarski @ X34 @ X35)))),
% 1.28/1.52      inference('cnf', [status(esa)], [l53_enumset1])).
% 1.28/1.52  thf('21', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.28/1.52  thf('22', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X1 @ X0 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['20', '21'])).
% 1.28/1.52  thf('23', plain,
% 1.28/1.52      (![X44 : $i, X45 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.28/1.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.28/1.52  thf('24', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_enumset1 @ X1 @ X0 @ X1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['22', '23'])).
% 1.28/1.52  thf(t125_enumset1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i,D:$i]:
% 1.28/1.52     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 1.28/1.52  thf('25', plain,
% 1.28/1.52      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X39 @ X38 @ X37 @ X36)
% 1.28/1.52           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 1.28/1.52      inference('cnf', [status(esa)], [t125_enumset1])).
% 1.28/1.52  thf('26', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k2_enumset1 @ X0 @ X1 @ X0 @ X1) = (k1_enumset1 @ X1 @ X1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['24', '25'])).
% 1.28/1.52  thf('27', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 1.28/1.52      inference('demod', [status(thm)], ['19', '26'])).
% 1.28/1.52  thf('28', plain,
% 1.28/1.52      (![X44 : $i, X45 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.28/1.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.28/1.52  thf('29', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('30', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('31', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('32', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['16', '29', '30', '31'])).
% 1.28/1.52  thf('33', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X0 @ X0 @ X1) = (k2_tarski @ X1 @ X0))),
% 1.28/1.52      inference('demod', [status(thm)], ['19', '26'])).
% 1.28/1.52  thf('34', plain,
% 1.28/1.52      (![X44 : $i, X45 : $i]:
% 1.28/1.52         ((k1_enumset1 @ X44 @ X44 @ X45) = (k2_tarski @ X44 @ X45))),
% 1.28/1.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.28/1.52  thf(l51_zfmisc_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.28/1.52  thf('35', plain,
% 1.28/1.52      (![X64 : $i, X65 : $i]:
% 1.28/1.52         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 1.28/1.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.28/1.52  thf('36', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['34', '35'])).
% 1.28/1.52  thf('37', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['33', '36'])).
% 1.28/1.52  thf('38', plain,
% 1.28/1.52      (![X64 : $i, X65 : $i]:
% 1.28/1.52         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 1.28/1.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.28/1.52  thf('39', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['37', '38'])).
% 1.28/1.52  thf('40', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 1.28/1.52          | (r2_hidden @ X0 @ 
% 1.28/1.52             (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.28/1.52      inference('demod', [status(thm)], ['32', '39'])).
% 1.28/1.52  thf('41', plain,
% 1.28/1.52      (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))
% 1.28/1.52        | (r2_hidden @ sk_A @ 
% 1.28/1.52           (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.28/1.52      inference('sup-', [status(thm)], ['7', '40'])).
% 1.28/1.52  thf('42', plain,
% 1.28/1.52      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.28/1.52         = (k2_tarski @ sk_A @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf(l97_xboole_1, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 1.28/1.52  thf('43', plain,
% 1.28/1.52      (![X12 : $i, X13 : $i]:
% 1.28/1.52         (r1_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k5_xboole_0 @ X12 @ X13))),
% 1.28/1.52      inference('cnf', [status(esa)], [l97_xboole_1])).
% 1.28/1.52  thf('44', plain,
% 1.28/1.52      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.28/1.52        (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['42', '43'])).
% 1.28/1.52  thf('45', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.52  thf('46', plain,
% 1.28/1.52      ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.28/1.52        (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 1.28/1.52      inference('demod', [status(thm)], ['44', '45'])).
% 1.28/1.52  thf('47', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('48', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('49', plain,
% 1.28/1.52      ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 1.28/1.52        (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.28/1.52      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.28/1.52  thf('50', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('51', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.28/1.52          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['1', '3'])).
% 1.28/1.52  thf('52', plain,
% 1.28/1.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.28/1.52         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.28/1.52  thf('53', plain,
% 1.28/1.52      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.28/1.52         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 1.28/1.52      inference('simplify', [status(thm)], ['52'])).
% 1.28/1.52  thf('54', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup-', [status(thm)], ['51', '53'])).
% 1.28/1.52  thf(t3_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]:
% 1.28/1.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.28/1.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.28/1.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.28/1.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.28/1.52  thf('55', plain,
% 1.28/1.52      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.28/1.52         (~ (r2_hidden @ X10 @ X8)
% 1.28/1.52          | ~ (r2_hidden @ X10 @ X11)
% 1.28/1.52          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.28/1.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.28/1.52  thf('56', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.28/1.52          | ~ (r2_hidden @ X1 @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['54', '55'])).
% 1.28/1.52  thf('57', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.28/1.52         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 1.28/1.52          | ~ (r2_hidden @ X0 @ X2))),
% 1.28/1.52      inference('sup-', [status(thm)], ['50', '56'])).
% 1.28/1.52  thf('58', plain,
% 1.28/1.52      (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.28/1.52      inference('sup-', [status(thm)], ['49', '57'])).
% 1.28/1.52  thf('59', plain,
% 1.28/1.52      ((r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 1.28/1.52      inference('clc', [status(thm)], ['41', '58'])).
% 1.28/1.52  thf('60', plain,
% 1.28/1.52      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.28/1.52         = (k2_tarski @ sk_A @ sk_B))),
% 1.28/1.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.28/1.52  thf('61', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('62', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['27', '28'])).
% 1.28/1.52  thf('63', plain,
% 1.28/1.52      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.28/1.52         = (k2_tarski @ sk_B @ sk_A))),
% 1.28/1.52      inference('demod', [status(thm)], ['60', '61', '62'])).
% 1.28/1.52  thf('64', plain,
% 1.28/1.52      (![X18 : $i, X19 : $i]:
% 1.28/1.52         ((k3_xboole_0 @ X18 @ X19)
% 1.28/1.52           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.28/1.52              (k5_xboole_0 @ X18 @ X19)))),
% 1.28/1.52      inference('demod', [status(thm)], ['9', '10'])).
% 1.28/1.52  thf('65', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.52  thf(t92_xboole_1, axiom,
% 1.28/1.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.28/1.52  thf('66', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.28/1.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.28/1.52  thf(t91_xboole_1, axiom,
% 1.28/1.52    (![A:$i,B:$i,C:$i]:
% 1.28/1.52     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.28/1.52       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.28/1.52  thf('67', plain,
% 1.28/1.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.28/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.28/1.52           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.28/1.52  thf('68', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.28/1.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['66', '67'])).
% 1.28/1.52  thf('69', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ X2) = (X2))),
% 1.28/1.52      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.28/1.52  thf('70', plain,
% 1.28/1.52      (![X18 : $i, X19 : $i]:
% 1.28/1.52         ((k3_xboole_0 @ X18 @ X19)
% 1.28/1.52           = (k5_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ 
% 1.28/1.52              (k5_xboole_0 @ X18 @ X19)))),
% 1.28/1.52      inference('demod', [status(thm)], ['9', '10'])).
% 1.28/1.52  thf('71', plain,
% 1.28/1.52      (![X0 : $i]:
% 1.28/1.52         ((k3_xboole_0 @ X0 @ X0)
% 1.28/1.52           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['69', '70'])).
% 1.28/1.52  thf(idempotence_k3_xboole_0, axiom,
% 1.28/1.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.28/1.52  thf('72', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 1.28/1.52      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.28/1.52  thf('73', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 1.28/1.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.28/1.52  thf('74', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.28/1.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.28/1.52  thf('75', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.28/1.52  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.28/1.52      inference('sup+', [status(thm)], ['74', '75'])).
% 1.28/1.52  thf('77', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('demod', [status(thm)], ['68', '76'])).
% 1.28/1.52  thf('78', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['65', '77'])).
% 1.28/1.52  thf('79', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k2_xboole_0 @ X1 @ X0)
% 1.28/1.52           = (k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['64', '78'])).
% 1.28/1.52  thf('80', plain,
% 1.28/1.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.28/1.52         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 1.28/1.52           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 1.28/1.52      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.28/1.52  thf('81', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((k2_xboole_0 @ X1 @ X0)
% 1.28/1.52           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.28/1.52      inference('demod', [status(thm)], ['79', '80'])).
% 1.28/1.52  thf('82', plain,
% 1.28/1.52      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 1.28/1.52         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 1.28/1.52            (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))))),
% 1.28/1.52      inference('sup+', [status(thm)], ['63', '81'])).
% 1.28/1.52  thf('83', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.28/1.52      inference('sup+', [status(thm)], ['37', '38'])).
% 1.28/1.52  thf('84', plain,
% 1.28/1.52      (![X0 : $i, X1 : $i]:
% 1.28/1.52         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.28/1.52      inference('sup+', [status(thm)], ['65', '77'])).
% 1.28/1.52  thf('85', plain,
% 1.28/1.52      (((k2_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)) = (sk_C_1))),
% 1.28/1.52      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.28/1.52  thf('86', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 1.28/1.52      inference('demod', [status(thm)], ['59', '85'])).
% 1.28/1.52  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 1.28/1.52  
% 1.28/1.52  % SZS output end Refutation
% 1.28/1.52  
% 1.35/1.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
