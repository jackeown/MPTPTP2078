%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KVXNWZxPT0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:44 EST 2020

% Result     : Theorem 26.21s
% Output     : Refutation 26.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 153 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  833 (1355 expanded)
%              Number of equality atoms :   59 ( 104 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

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

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( r1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(eq_fact,[status(thm)],['16'])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('27',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k5_xboole_0 @ X13 @ ( k5_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','42'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','41'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k5_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('50',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_tarski @ sk_B @ sk_A ) ) @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','62'])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X20 @ X19 )
      = ( k2_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('66',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_A @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KVXNWZxPT0
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:09:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 26.21/26.40  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.21/26.40  % Solved by: fo/fo7.sh
% 26.21/26.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.21/26.40  % done 10605 iterations in 25.929s
% 26.21/26.40  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.21/26.40  % SZS output start Refutation
% 26.21/26.40  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 26.21/26.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.21/26.40  thf(sk_B_type, type, sk_B: $i).
% 26.21/26.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.21/26.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 26.21/26.40  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.21/26.40  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 26.21/26.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 26.21/26.40  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 26.21/26.40  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 26.21/26.40  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 26.21/26.40  thf(sk_A_type, type, sk_A: $i).
% 26.21/26.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 26.21/26.40  thf(t63_zfmisc_1, conjecture,
% 26.21/26.40    (![A:$i,B:$i,C:$i]:
% 26.21/26.40     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 26.21/26.40       ( r2_hidden @ A @ C ) ))).
% 26.21/26.40  thf(zf_stmt_0, negated_conjecture,
% 26.21/26.40    (~( ![A:$i,B:$i,C:$i]:
% 26.21/26.40        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 26.21/26.40          ( r2_hidden @ A @ C ) ) )),
% 26.21/26.40    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 26.21/26.40  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.21/26.40  thf(t70_enumset1, axiom,
% 26.21/26.40    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 26.21/26.40  thf('1', plain,
% 26.21/26.40      (![X33 : $i, X34 : $i]:
% 26.21/26.40         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 26.21/26.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 26.21/26.40  thf(d1_enumset1, axiom,
% 26.21/26.40    (![A:$i,B:$i,C:$i,D:$i]:
% 26.21/26.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 26.21/26.40       ( ![E:$i]:
% 26.21/26.40         ( ( r2_hidden @ E @ D ) <=>
% 26.21/26.40           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 26.21/26.40  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 26.21/26.40  thf(zf_stmt_2, axiom,
% 26.21/26.40    (![E:$i,C:$i,B:$i,A:$i]:
% 26.21/26.40     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 26.21/26.40       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 26.21/26.40  thf(zf_stmt_3, axiom,
% 26.21/26.40    (![A:$i,B:$i,C:$i,D:$i]:
% 26.21/26.40     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 26.21/26.40       ( ![E:$i]:
% 26.21/26.40         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 26.21/26.40  thf('2', plain,
% 26.21/26.40      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 26.21/26.40         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 26.21/26.40          | (r2_hidden @ X26 @ X30)
% 26.21/26.40          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.21/26.40  thf('3', plain,
% 26.21/26.40      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 26.21/26.40         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 26.21/26.40          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 26.21/26.40      inference('simplify', [status(thm)], ['2'])).
% 26.21/26.40  thf('4', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 26.21/26.40          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 26.21/26.40      inference('sup+', [status(thm)], ['1', '3'])).
% 26.21/26.40  thf('5', plain,
% 26.21/26.40      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 26.21/26.40         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.21/26.40  thf('6', plain,
% 26.21/26.40      (![X21 : $i, X23 : $i, X24 : $i]:
% 26.21/26.40         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 26.21/26.40      inference('simplify', [status(thm)], ['5'])).
% 26.21/26.40  thf('7', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 26.21/26.40      inference('sup-', [status(thm)], ['4', '6'])).
% 26.21/26.40  thf('8', plain,
% 26.21/26.40      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 26.21/26.40         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 26.21/26.40          | ((X22) = (X23))
% 26.21/26.40          | ((X22) = (X24))
% 26.21/26.40          | ((X22) = (X25)))),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_2])).
% 26.21/26.40  thf(t3_xboole_0, axiom,
% 26.21/26.40    (![A:$i,B:$i]:
% 26.21/26.40     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 26.21/26.40            ( r1_xboole_0 @ A @ B ) ) ) & 
% 26.21/26.40       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 26.21/26.40            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 26.21/26.40  thf('9', plain,
% 26.21/26.40      (![X6 : $i, X7 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('10', plain,
% 26.21/26.40      (![X33 : $i, X34 : $i]:
% 26.21/26.40         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 26.21/26.40      inference('cnf', [status(esa)], [t70_enumset1])).
% 26.21/26.40  thf('11', plain,
% 26.21/26.40      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 26.21/26.40         (~ (r2_hidden @ X31 @ X30)
% 26.21/26.40          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 26.21/26.40          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_3])).
% 26.21/26.40  thf('12', plain,
% 26.21/26.40      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 26.21/26.40         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 26.21/26.40          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 26.21/26.40      inference('simplify', [status(thm)], ['11'])).
% 26.21/26.40  thf('13', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 26.21/26.40          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 26.21/26.40      inference('sup-', [status(thm)], ['10', '12'])).
% 26.21/26.40  thf('14', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 26.21/26.40          | ~ (zip_tseitin_0 @ (sk_C @ X2 @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ 
% 26.21/26.40               X1))),
% 26.21/26.40      inference('sup-', [status(thm)], ['9', '13'])).
% 26.21/26.40  thf('15', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ X0 @ X1) @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['8', '14'])).
% 26.21/26.40  thf('16', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ (k2_tarski @ X0 @ X1) @ X2)
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 26.21/26.40      inference('simplify', [status(thm)], ['15'])).
% 26.21/26.40  thf('17', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (((X0) != (X1))
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1))
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2))),
% 26.21/26.40      inference('eq_fact', [status(thm)], ['16'])).
% 26.21/26.40  thf('18', plain,
% 26.21/26.40      (![X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ (k2_tarski @ X1 @ X1) @ X2)
% 26.21/26.40          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 26.21/26.40      inference('simplify', [status(thm)], ['17'])).
% 26.21/26.40  thf('19', plain,
% 26.21/26.40      (![X6 : $i, X7 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('20', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((r2_hidden @ X0 @ X1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))),
% 26.21/26.40      inference('sup+', [status(thm)], ['18', '19'])).
% 26.21/26.40  thf('21', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 26.21/26.40      inference('simplify', [status(thm)], ['20'])).
% 26.21/26.40  thf('22', plain,
% 26.21/26.40      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 26.21/26.40         = (k2_tarski @ sk_A @ sk_B))),
% 26.21/26.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.21/26.40  thf(commutativity_k2_tarski, axiom,
% 26.21/26.40    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 26.21/26.40  thf('23', plain,
% 26.21/26.40      (![X19 : $i, X20 : $i]:
% 26.21/26.40         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 26.21/26.40      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 26.21/26.40  thf('24', plain,
% 26.21/26.40      (![X19 : $i, X20 : $i]:
% 26.21/26.40         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 26.21/26.40      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 26.21/26.40  thf('25', plain,
% 26.21/26.40      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 26.21/26.40         = (k2_tarski @ sk_B @ sk_A))),
% 26.21/26.40      inference('demod', [status(thm)], ['22', '23', '24'])).
% 26.21/26.40  thf(l97_xboole_1, axiom,
% 26.21/26.40    (![A:$i,B:$i]:
% 26.21/26.40     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 26.21/26.40  thf('26', plain,
% 26.21/26.40      (![X10 : $i, X11 : $i]:
% 26.21/26.40         (r1_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k5_xboole_0 @ X10 @ X11))),
% 26.21/26.40      inference('cnf', [status(esa)], [l97_xboole_1])).
% 26.21/26.40  thf('27', plain,
% 26.21/26.40      ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 26.21/26.40        (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1))),
% 26.21/26.40      inference('sup+', [status(thm)], ['25', '26'])).
% 26.21/26.40  thf(t91_xboole_1, axiom,
% 26.21/26.40    (![A:$i,B:$i,C:$i]:
% 26.21/26.40     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 26.21/26.40       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 26.21/26.40  thf('28', plain,
% 26.21/26.40      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 26.21/26.40           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 26.21/26.40      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.21/26.40  thf(t92_xboole_1, axiom,
% 26.21/26.40    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 26.21/26.40  thf('29', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 26.21/26.40      inference('cnf', [status(esa)], [t92_xboole_1])).
% 26.21/26.40  thf('30', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))
% 26.21/26.40           = (k1_xboole_0))),
% 26.21/26.40      inference('sup+', [status(thm)], ['28', '29'])).
% 26.21/26.40  thf('31', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ X16) = (k1_xboole_0))),
% 26.21/26.40      inference('cnf', [status(esa)], [t92_xboole_1])).
% 26.21/26.40  thf('32', plain,
% 26.21/26.40      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 26.21/26.40           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 26.21/26.40      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.21/26.40  thf('33', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 26.21/26.40           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.21/26.40      inference('sup+', [status(thm)], ['31', '32'])).
% 26.21/26.40  thf(t95_xboole_1, axiom,
% 26.21/26.40    (![A:$i,B:$i]:
% 26.21/26.40     ( ( k3_xboole_0 @ A @ B ) =
% 26.21/26.40       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 26.21/26.40  thf('34', plain,
% 26.21/26.40      (![X17 : $i, X18 : $i]:
% 26.21/26.40         ((k3_xboole_0 @ X17 @ X18)
% 26.21/26.40           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 26.21/26.40              (k2_xboole_0 @ X17 @ X18)))),
% 26.21/26.40      inference('cnf', [status(esa)], [t95_xboole_1])).
% 26.21/26.40  thf('35', plain,
% 26.21/26.40      (![X13 : $i, X14 : $i, X15 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ (k5_xboole_0 @ X13 @ X14) @ X15)
% 26.21/26.40           = (k5_xboole_0 @ X13 @ (k5_xboole_0 @ X14 @ X15)))),
% 26.21/26.40      inference('cnf', [status(esa)], [t91_xboole_1])).
% 26.21/26.40  thf('36', plain,
% 26.21/26.40      (![X17 : $i, X18 : $i]:
% 26.21/26.40         ((k3_xboole_0 @ X17 @ X18)
% 26.21/26.40           = (k5_xboole_0 @ X17 @ 
% 26.21/26.40              (k5_xboole_0 @ X18 @ (k2_xboole_0 @ X17 @ X18))))),
% 26.21/26.40      inference('demod', [status(thm)], ['34', '35'])).
% 26.21/26.40  thf('37', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 26.21/26.40           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.21/26.40      inference('sup+', [status(thm)], ['31', '32'])).
% 26.21/26.40  thf('38', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0))
% 26.21/26.40           = (k3_xboole_0 @ X0 @ X0))),
% 26.21/26.40      inference('sup+', [status(thm)], ['36', '37'])).
% 26.21/26.40  thf(idempotence_k2_xboole_0, axiom,
% 26.21/26.40    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 26.21/26.40  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 26.21/26.40      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 26.21/26.40  thf(idempotence_k3_xboole_0, axiom,
% 26.21/26.40    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 26.21/26.40  thf('40', plain, (![X1 : $i]: ((k3_xboole_0 @ X1 @ X1) = (X1))),
% 26.21/26.40      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 26.21/26.40  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 26.21/26.40      inference('demod', [status(thm)], ['38', '39', '40'])).
% 26.21/26.40  thf('42', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.21/26.40      inference('demod', [status(thm)], ['33', '41'])).
% 26.21/26.40  thf('43', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 26.21/26.40           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 26.21/26.40      inference('sup+', [status(thm)], ['30', '42'])).
% 26.21/26.40  thf(t5_boole, axiom,
% 26.21/26.40    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 26.21/26.40  thf('44', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 26.21/26.40      inference('cnf', [status(esa)], [t5_boole])).
% 26.21/26.40  thf('45', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)) = (X1))),
% 26.21/26.40      inference('demod', [status(thm)], ['43', '44'])).
% 26.21/26.40  thf('46', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]:
% 26.21/26.40         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 26.21/26.40      inference('demod', [status(thm)], ['33', '41'])).
% 26.21/26.40  thf('47', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X0 @ X1) = (k5_xboole_0 @ X1 @ X0))),
% 26.21/26.40      inference('sup+', [status(thm)], ['45', '46'])).
% 26.21/26.40  thf('48', plain,
% 26.21/26.40      ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ 
% 26.21/26.40        (k5_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A)))),
% 26.21/26.40      inference('demod', [status(thm)], ['27', '47'])).
% 26.21/26.40  thf('49', plain,
% 26.21/26.40      (![X6 : $i, X7 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf(t1_xboole_0, axiom,
% 26.21/26.40    (![A:$i,B:$i,C:$i]:
% 26.21/26.40     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 26.21/26.40       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 26.21/26.40  thf('50', plain,
% 26.21/26.40      (![X2 : $i, X3 : $i, X5 : $i]:
% 26.21/26.40         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 26.21/26.40          | (r2_hidden @ X2 @ X3)
% 26.21/26.40          | ~ (r2_hidden @ X2 @ X5))),
% 26.21/26.40      inference('cnf', [status(esa)], [t1_xboole_0])).
% 26.21/26.40  thf('51', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X0 @ X1)
% 26.21/26.40          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 26.21/26.40          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 26.21/26.40      inference('sup-', [status(thm)], ['49', '50'])).
% 26.21/26.40  thf('52', plain,
% 26.21/26.40      (![X6 : $i, X7 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('53', plain,
% 26.21/26.40      (![X6 : $i, X8 : $i, X9 : $i]:
% 26.21/26.40         (~ (r2_hidden @ X8 @ X6)
% 26.21/26.40          | ~ (r2_hidden @ X8 @ X9)
% 26.21/26.40          | ~ (r1_xboole_0 @ X6 @ X9))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('54', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X0 @ X1)
% 26.21/26.40          | ~ (r1_xboole_0 @ X0 @ X2)
% 26.21/26.40          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['52', '53'])).
% 26.21/26.40  thf('55', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r2_hidden @ (sk_C @ X2 @ X0) @ X1)
% 26.21/26.40          | (r1_xboole_0 @ X0 @ X2)
% 26.21/26.40          | ~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 26.21/26.40          | (r1_xboole_0 @ X0 @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['51', '54'])).
% 26.21/26.40  thf('56', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0))
% 26.21/26.40          | (r1_xboole_0 @ X0 @ X2)
% 26.21/26.40          | (r2_hidden @ (sk_C @ X2 @ X0) @ X1))),
% 26.21/26.40      inference('simplify', [status(thm)], ['55'])).
% 26.21/26.40  thf('57', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         ((r2_hidden @ (sk_C @ X0 @ (k2_tarski @ sk_B @ sk_A)) @ sk_C_1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))),
% 26.21/26.40      inference('sup-', [status(thm)], ['48', '56'])).
% 26.21/26.40  thf('58', plain,
% 26.21/26.40      (![X6 : $i, X7 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('59', plain,
% 26.21/26.40      (![X6 : $i, X8 : $i, X9 : $i]:
% 26.21/26.40         (~ (r2_hidden @ X8 @ X6)
% 26.21/26.40          | ~ (r2_hidden @ X8 @ X9)
% 26.21/26.40          | ~ (r1_xboole_0 @ X6 @ X9))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('60', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ X1 @ X0)
% 26.21/26.40          | ~ (r1_xboole_0 @ X0 @ X2)
% 26.21/26.40          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['58', '59'])).
% 26.21/26.40  thf('61', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         ((r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0)
% 26.21/26.40          | ~ (r1_xboole_0 @ X0 @ sk_C_1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))),
% 26.21/26.40      inference('sup-', [status(thm)], ['57', '60'])).
% 26.21/26.40  thf('62', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         (~ (r1_xboole_0 @ X0 @ sk_C_1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ X0))),
% 26.21/26.40      inference('simplify', [status(thm)], ['61'])).
% 26.21/26.40  thf('63', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         ((r2_hidden @ X0 @ sk_C_1)
% 26.21/26.40          | (r1_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ (k2_tarski @ X0 @ X0)))),
% 26.21/26.40      inference('sup-', [status(thm)], ['21', '62'])).
% 26.21/26.40  thf('64', plain,
% 26.21/26.40      (![X19 : $i, X20 : $i]:
% 26.21/26.40         ((k2_tarski @ X20 @ X19) = (k2_tarski @ X19 @ X20))),
% 26.21/26.40      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 26.21/26.40  thf('65', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 26.21/26.40      inference('sup-', [status(thm)], ['4', '6'])).
% 26.21/26.40  thf('66', plain,
% 26.21/26.40      (![X6 : $i, X8 : $i, X9 : $i]:
% 26.21/26.40         (~ (r2_hidden @ X8 @ X6)
% 26.21/26.40          | ~ (r2_hidden @ X8 @ X9)
% 26.21/26.40          | ~ (r1_xboole_0 @ X6 @ X9))),
% 26.21/26.40      inference('cnf', [status(esa)], [t3_xboole_0])).
% 26.21/26.40  thf('67', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 26.21/26.40          | ~ (r2_hidden @ X1 @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['65', '66'])).
% 26.21/26.40  thf('68', plain,
% 26.21/26.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.21/26.40         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 26.21/26.40          | ~ (r2_hidden @ X0 @ X2))),
% 26.21/26.40      inference('sup-', [status(thm)], ['64', '67'])).
% 26.21/26.40  thf('69', plain,
% 26.21/26.40      (![X0 : $i]:
% 26.21/26.40         ((r2_hidden @ X0 @ sk_C_1)
% 26.21/26.40          | ~ (r2_hidden @ sk_A @ (k2_tarski @ X0 @ X0)))),
% 26.21/26.40      inference('sup-', [status(thm)], ['63', '68'])).
% 26.21/26.40  thf('70', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 26.21/26.40      inference('sup-', [status(thm)], ['7', '69'])).
% 26.21/26.40  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 26.21/26.40  
% 26.21/26.40  % SZS output end Refutation
% 26.21/26.40  
% 26.21/26.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
