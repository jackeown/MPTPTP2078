%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZrP6VHIbj

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:19 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 144 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  739 (1236 expanded)
%              Number of equality atoms :   60 ( 100 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
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

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

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
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t51_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
          = ( k1_tarski @ B ) )
       => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t51_zfmisc_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ sk_A ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('34',plain,
    ( ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('41',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('42',plain,(
    ! [X63: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X63 ) )
      = X63 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X61 @ X62 ) )
      = ( k2_xboole_0 @ X61 @ X62 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','45'])).

thf('47',plain,
    ( ( k1_tarski @ sk_B )
    = ( k5_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','46'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ sk_A )
      | ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZrP6VHIbj
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.54/1.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.54/1.74  % Solved by: fo/fo7.sh
% 1.54/1.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.54/1.74  % done 1349 iterations in 1.280s
% 1.54/1.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.54/1.74  % SZS output start Refutation
% 1.54/1.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.54/1.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.54/1.74  thf(sk_B_type, type, sk_B: $i).
% 1.54/1.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.54/1.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.54/1.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.54/1.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.54/1.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.54/1.74  thf(sk_A_type, type, sk_A: $i).
% 1.54/1.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.54/1.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.54/1.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.54/1.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.54/1.74  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.54/1.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.54/1.74  thf(t70_enumset1, axiom,
% 1.54/1.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.54/1.74  thf('0', plain,
% 1.54/1.74      (![X34 : $i, X35 : $i]:
% 1.54/1.74         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.54/1.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.54/1.74  thf(d1_enumset1, axiom,
% 1.54/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.54/1.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.54/1.74       ( ![E:$i]:
% 1.54/1.74         ( ( r2_hidden @ E @ D ) <=>
% 1.54/1.74           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.54/1.74  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.54/1.74  thf(zf_stmt_1, axiom,
% 1.54/1.74    (![E:$i,C:$i,B:$i,A:$i]:
% 1.54/1.74     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.54/1.74       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.54/1.74  thf(zf_stmt_2, axiom,
% 1.54/1.74    (![A:$i,B:$i,C:$i,D:$i]:
% 1.54/1.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.54/1.74       ( ![E:$i]:
% 1.54/1.74         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.54/1.74  thf('1', plain,
% 1.54/1.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.54/1.74         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 1.54/1.74          | (r2_hidden @ X26 @ X30)
% 1.54/1.74          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.54/1.74  thf('2', plain,
% 1.54/1.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.54/1.74         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 1.54/1.74          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 1.54/1.74      inference('simplify', [status(thm)], ['1'])).
% 1.54/1.74  thf('3', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.54/1.74         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.54/1.74          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.54/1.74      inference('sup+', [status(thm)], ['0', '2'])).
% 1.54/1.74  thf('4', plain,
% 1.54/1.74      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.54/1.74         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.54/1.74  thf('5', plain,
% 1.54/1.74      (![X21 : $i, X23 : $i, X24 : $i]:
% 1.54/1.74         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 1.54/1.74      inference('simplify', [status(thm)], ['4'])).
% 1.54/1.74  thf('6', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.54/1.74      inference('sup-', [status(thm)], ['3', '5'])).
% 1.54/1.74  thf(t79_xboole_1, axiom,
% 1.54/1.74    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.54/1.74  thf('7', plain,
% 1.54/1.74      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 1.54/1.74      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.54/1.74  thf('8', plain,
% 1.54/1.74      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.54/1.74         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 1.54/1.74          | ((X22) = (X23))
% 1.54/1.74          | ((X22) = (X24))
% 1.54/1.74          | ((X22) = (X25)))),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.54/1.74  thf(t3_xboole_0, axiom,
% 1.54/1.74    (![A:$i,B:$i]:
% 1.54/1.74     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.54/1.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.54/1.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.54/1.74            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.54/1.74  thf('9', plain,
% 1.54/1.74      (![X7 : $i, X8 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.54/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.54/1.74  thf(t69_enumset1, axiom,
% 1.54/1.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.54/1.74  thf('10', plain,
% 1.54/1.74      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.54/1.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.54/1.74  thf('11', plain,
% 1.54/1.74      (![X34 : $i, X35 : $i]:
% 1.54/1.74         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 1.54/1.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.54/1.74  thf('12', plain,
% 1.54/1.74      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X31 @ X30)
% 1.54/1.74          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 1.54/1.74          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.54/1.74  thf('13', plain,
% 1.54/1.74      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 1.54/1.74         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 1.54/1.74          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 1.54/1.74      inference('simplify', [status(thm)], ['12'])).
% 1.54/1.74  thf('14', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.54/1.74          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.54/1.74      inference('sup-', [status(thm)], ['11', '13'])).
% 1.54/1.74  thf('15', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.54/1.74          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.54/1.74      inference('sup-', [status(thm)], ['10', '14'])).
% 1.54/1.74  thf('16', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.54/1.74          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 1.54/1.74      inference('sup-', [status(thm)], ['9', '15'])).
% 1.54/1.74  thf('17', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.54/1.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.54/1.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 1.54/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.54/1.74      inference('sup-', [status(thm)], ['8', '16'])).
% 1.54/1.74  thf('18', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.54/1.74          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 1.54/1.74      inference('simplify', [status(thm)], ['17'])).
% 1.54/1.74  thf('19', plain,
% 1.54/1.74      (![X7 : $i, X8 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 1.54/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.54/1.74  thf('20', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 1.54/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.54/1.74          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.54/1.74      inference('sup+', [status(thm)], ['18', '19'])).
% 1.54/1.74  thf('21', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.54/1.74          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.54/1.74      inference('simplify', [status(thm)], ['20'])).
% 1.54/1.74  thf(t51_zfmisc_1, conjecture,
% 1.54/1.74    (![A:$i,B:$i]:
% 1.54/1.74     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 1.54/1.74       ( r2_hidden @ B @ A ) ))).
% 1.54/1.74  thf(zf_stmt_3, negated_conjecture,
% 1.54/1.74    (~( ![A:$i,B:$i]:
% 1.54/1.74        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 1.54/1.74          ( r2_hidden @ B @ A ) ) )),
% 1.54/1.74    inference('cnf.neg', [status(esa)], [t51_zfmisc_1])).
% 1.54/1.74  thf('22', plain,
% 1.54/1.74      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.54/1.74  thf(t100_xboole_1, axiom,
% 1.54/1.74    (![A:$i,B:$i]:
% 1.54/1.74     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.54/1.74  thf('23', plain,
% 1.54/1.74      (![X11 : $i, X12 : $i]:
% 1.54/1.74         ((k4_xboole_0 @ X11 @ X12)
% 1.54/1.74           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.54/1.74  thf('24', plain,
% 1.54/1.74      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 1.54/1.74         = (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['22', '23'])).
% 1.54/1.74  thf(t91_xboole_1, axiom,
% 1.54/1.74    (![A:$i,B:$i,C:$i]:
% 1.54/1.74     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.54/1.74       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.54/1.74  thf('25', plain,
% 1.54/1.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.54/1.74           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.54/1.74  thf('26', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ X0)
% 1.54/1.74           = (k5_xboole_0 @ sk_A @ (k5_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['24', '25'])).
% 1.54/1.74  thf(commutativity_k5_xboole_0, axiom,
% 1.54/1.74    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.54/1.74  thf('27', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.54/1.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.54/1.74  thf(t92_xboole_1, axiom,
% 1.54/1.74    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.54/1.74  thf('28', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.54/1.74      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.54/1.74  thf('29', plain,
% 1.54/1.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.54/1.74           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.54/1.74  thf('30', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.54/1.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['28', '29'])).
% 1.54/1.74  thf('31', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ k1_xboole_0 @ X1)
% 1.54/1.74           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['27', '30'])).
% 1.54/1.74  thf('32', plain,
% 1.54/1.74      (((k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B))
% 1.54/1.74         = (k5_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ sk_A))),
% 1.54/1.74      inference('sup+', [status(thm)], ['26', '31'])).
% 1.54/1.74  thf('33', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.54/1.74      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.54/1.74  thf('34', plain,
% 1.54/1.74      (((k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_B))
% 1.54/1.74         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.54/1.74      inference('demod', [status(thm)], ['32', '33'])).
% 1.54/1.74  thf('35', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.54/1.74           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['28', '29'])).
% 1.54/1.74  thf(t95_xboole_1, axiom,
% 1.54/1.74    (![A:$i,B:$i]:
% 1.54/1.74     ( ( k3_xboole_0 @ A @ B ) =
% 1.54/1.74       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.54/1.74  thf('36', plain,
% 1.54/1.74      (![X19 : $i, X20 : $i]:
% 1.54/1.74         ((k3_xboole_0 @ X19 @ X20)
% 1.54/1.74           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 1.54/1.74              (k2_xboole_0 @ X19 @ X20)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.54/1.74  thf('37', plain,
% 1.54/1.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.54/1.74         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.54/1.74           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.54/1.74  thf('38', plain,
% 1.54/1.74      (![X19 : $i, X20 : $i]:
% 1.54/1.74         ((k3_xboole_0 @ X19 @ X20)
% 1.54/1.74           = (k5_xboole_0 @ X19 @ 
% 1.54/1.74              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 1.54/1.74      inference('demod', [status(thm)], ['36', '37'])).
% 1.54/1.74  thf('39', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         ((k3_xboole_0 @ X0 @ X0)
% 1.54/1.74           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.54/1.74      inference('sup+', [status(thm)], ['35', '38'])).
% 1.54/1.74  thf(idempotence_k3_xboole_0, axiom,
% 1.54/1.74    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.54/1.74  thf('40', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 1.54/1.74      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.54/1.74  thf('41', plain,
% 1.54/1.74      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.54/1.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.54/1.74  thf(t31_zfmisc_1, axiom,
% 1.54/1.74    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 1.54/1.74  thf('42', plain, (![X63 : $i]: ((k3_tarski @ (k1_tarski @ X63)) = (X63))),
% 1.54/1.74      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 1.54/1.74  thf('43', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.54/1.74      inference('sup+', [status(thm)], ['41', '42'])).
% 1.54/1.74  thf(l51_zfmisc_1, axiom,
% 1.54/1.74    (![A:$i,B:$i]:
% 1.54/1.74     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.54/1.74  thf('44', plain,
% 1.54/1.74      (![X61 : $i, X62 : $i]:
% 1.54/1.74         ((k3_tarski @ (k2_tarski @ X61 @ X62)) = (k2_xboole_0 @ X61 @ X62))),
% 1.54/1.74      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.54/1.74  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.54/1.74      inference('demod', [status(thm)], ['43', '44'])).
% 1.54/1.74  thf('46', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 1.54/1.74      inference('demod', [status(thm)], ['39', '40', '45'])).
% 1.54/1.74  thf('47', plain,
% 1.54/1.74      (((k1_tarski @ sk_B)
% 1.54/1.74         = (k5_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.54/1.74      inference('demod', [status(thm)], ['34', '46'])).
% 1.54/1.74  thf(t1_xboole_0, axiom,
% 1.54/1.74    (![A:$i,B:$i,C:$i]:
% 1.54/1.74     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.54/1.74       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.54/1.74  thf('48', plain,
% 1.54/1.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.54/1.74         ((r2_hidden @ X3 @ X4)
% 1.54/1.74          | (r2_hidden @ X3 @ X5)
% 1.54/1.74          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 1.54/1.74      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.54/1.74  thf('49', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.54/1.74          | (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 1.54/1.74          | (r2_hidden @ X0 @ sk_A))),
% 1.54/1.74      inference('sup-', [status(thm)], ['47', '48'])).
% 1.54/1.74  thf('50', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 1.54/1.74          | (r2_hidden @ sk_B @ sk_A)
% 1.54/1.74          | (r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 1.54/1.74      inference('sup-', [status(thm)], ['21', '49'])).
% 1.54/1.74  thf('51', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.54/1.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.54/1.74  thf('52', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         ((r2_hidden @ sk_B @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 1.54/1.74          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 1.54/1.74      inference('clc', [status(thm)], ['50', '51'])).
% 1.54/1.74  thf('53', plain,
% 1.54/1.74      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X9 @ X7)
% 1.54/1.74          | ~ (r2_hidden @ X9 @ X10)
% 1.54/1.74          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.54/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.54/1.74  thf('54', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X1)
% 1.54/1.74          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ X0)
% 1.54/1.74          | ~ (r2_hidden @ sk_B @ X0))),
% 1.54/1.74      inference('sup-', [status(thm)], ['52', '53'])).
% 1.54/1.74  thf('55', plain,
% 1.54/1.74      (![X0 : $i]:
% 1.54/1.74         (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 1.54/1.74          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 1.54/1.74      inference('sup-', [status(thm)], ['7', '54'])).
% 1.54/1.74  thf('56', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.54/1.74          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.54/1.74      inference('simplify', [status(thm)], ['20'])).
% 1.54/1.74  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)),
% 1.54/1.74      inference('clc', [status(thm)], ['55', '56'])).
% 1.54/1.74  thf('58', plain,
% 1.54/1.74      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 1.54/1.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.54/1.74  thf('59', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.54/1.74      inference('sup-', [status(thm)], ['3', '5'])).
% 1.54/1.74  thf('60', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.54/1.74      inference('sup+', [status(thm)], ['58', '59'])).
% 1.54/1.74  thf('61', plain,
% 1.54/1.74      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.54/1.74         (~ (r2_hidden @ X9 @ X7)
% 1.54/1.74          | ~ (r2_hidden @ X9 @ X10)
% 1.54/1.74          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.54/1.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.54/1.74  thf('62', plain,
% 1.54/1.74      (![X0 : $i, X1 : $i]:
% 1.54/1.74         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.54/1.74      inference('sup-', [status(thm)], ['60', '61'])).
% 1.54/1.74  thf('63', plain, (![X0 : $i]: ~ (r2_hidden @ sk_B @ X0)),
% 1.54/1.74      inference('sup-', [status(thm)], ['57', '62'])).
% 1.54/1.74  thf('64', plain, ($false), inference('sup-', [status(thm)], ['6', '63'])).
% 1.54/1.74  
% 1.54/1.74  % SZS output end Refutation
% 1.54/1.74  
% 1.54/1.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
