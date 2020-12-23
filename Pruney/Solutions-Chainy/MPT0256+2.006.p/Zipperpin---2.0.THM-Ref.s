%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCQVXY2thD

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:19 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 116 expanded)
%              Number of leaves         :   24 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  749 (1109 expanded)
%              Number of equality atoms :   35 (  59 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X28 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) )
      | ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X19: $i,X21: $i,X22: $i] :
      ~ ( zip_tseitin_0 @ X19 @ X21 @ X22 @ X19 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( X20 = X21 )
      | ( X20 = X22 )
      | ( X20 = X23 ) ) ),
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

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ( X28
       != ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_enumset1 @ X27 @ X26 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X6 ) )
      | ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k5_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ ( k5_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('36',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ sk_A )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCQVXY2thD
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 627 iterations in 0.481s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(t70_enumset1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      (![X32 : $i, X33 : $i]:
% 0.75/0.93         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.93  thf(d1_enumset1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.93       ( ![E:$i]:
% 0.75/0.93         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.93           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.93  thf(zf_stmt_1, axiom,
% 0.75/0.93    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.93     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.93       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.93       ( ![E:$i]:
% 0.75/0.93         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X24 @ X25 @ X26 @ X27)
% 0.75/0.93          | (r2_hidden @ X24 @ X28)
% 0.75/0.93          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.93  thf('2', plain,
% 0.75/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.93         ((r2_hidden @ X24 @ (k1_enumset1 @ X27 @ X26 @ X25))
% 0.75/0.93          | (zip_tseitin_0 @ X24 @ X25 @ X26 @ X27))),
% 0.75/0.93      inference('simplify', [status(thm)], ['1'])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.93          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.93      inference('sup+', [status(thm)], ['0', '2'])).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.93         (((X20) != (X19)) | ~ (zip_tseitin_0 @ X20 @ X21 @ X22 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      (![X19 : $i, X21 : $i, X22 : $i]:
% 0.75/0.93         ~ (zip_tseitin_0 @ X19 @ X21 @ X22 @ X19)),
% 0.75/0.93      inference('simplify', [status(thm)], ['4'])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['3', '5'])).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.93         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.75/0.93          | ((X20) = (X21))
% 0.75/0.93          | ((X20) = (X22))
% 0.75/0.93          | ((X20) = (X23)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.93  thf(t3_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.75/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.75/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.75/0.93  thf('8', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.93  thf(t69_enumset1, axiom,
% 0.75/0.93    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.93  thf('9', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.75/0.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X32 : $i, X33 : $i]:
% 0.75/0.93         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.93  thf('11', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X29 @ X28)
% 0.75/0.93          | ~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.75/0.93          | ((X28) != (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X25 : $i, X26 : $i, X27 : $i, X29 : $i]:
% 0.75/0.93         (~ (zip_tseitin_0 @ X29 @ X25 @ X26 @ X27)
% 0.75/0.93          | ~ (r2_hidden @ X29 @ (k1_enumset1 @ X27 @ X26 @ X25)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.93          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['10', '12'])).
% 0.75/0.93  thf('14', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.93          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['9', '13'])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.75/0.93          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['8', '14'])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.75/0.93          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.75/0.93          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.75/0.93          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '15'])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.75/0.93          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.93  thf(t1_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.75/0.93       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.93         ((r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X6))
% 0.75/0.93          | (r2_hidden @ X3 @ X4)
% 0.75/0.93          | ~ (r2_hidden @ X3 @ X6))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X0 @ X1)
% 0.75/0.93          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.75/0.93          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k5_xboole_0 @ X2 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      (![X7 : $i, X8 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.75/0.93      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.93  thf(t51_zfmisc_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.75/0.93       ( r2_hidden @ B @ A ) ))).
% 0.75/0.93  thf(zf_stmt_3, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i]:
% 0.75/0.93        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.75/0.93          ( r2_hidden @ B @ A ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t51_zfmisc_1])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.93  thf(t95_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( k3_xboole_0 @ A @ B ) =
% 0.75/0.93       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.75/0.93  thf('23', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k3_xboole_0 @ X17 @ X18)
% 0.75/0.93           = (k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ 
% 0.75/0.93              (k2_xboole_0 @ X17 @ X18)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.75/0.93  thf(commutativity_k5_xboole_0, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.75/0.93  thf('24', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X17 : $i, X18 : $i]:
% 0.75/0.93         ((k3_xboole_0 @ X17 @ X18)
% 0.75/0.93           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.75/0.93              (k5_xboole_0 @ X17 @ X18)))),
% 0.75/0.93      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/0.93  thf('26', plain,
% 0.75/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.93         ((r2_hidden @ X3 @ X4)
% 0.75/0.93          | (r2_hidden @ X3 @ X5)
% 0.75/0.93          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.93          | (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.75/0.93          | (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.93  thf('28', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.75/0.93          | (r2_hidden @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.93          | (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['22', '27'])).
% 0.75/0.93  thf('29', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.93          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.93             (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.93          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.93             (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['21', '28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X9 @ X7)
% 0.75/0.94          | ~ (r2_hidden @ X9 @ X10)
% 0.75/0.94          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ X0 @ X1)
% 0.75/0.94          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.75/0.94          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.75/0.94      inference('sup-', [status(thm)], ['30', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94           (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | ~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.75/0.94               (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['29', '32'])).
% 0.75/0.94  thf('34', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf(l97_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         (r1_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ (k5_xboole_0 @ X11 @ X12))),
% 0.75/0.94      inference('cnf', [status(esa)], [l97_xboole_1])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      ((r1_xboole_0 @ (k1_tarski @ sk_B) @ 
% 0.75/0.94        (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['34', '35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94           (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['33', '36'])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94             (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k3_xboole_0 @ X17 @ X18)
% 0.75/0.94           = (k5_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ 
% 0.75/0.94              (k5_xboole_0 @ X17 @ X18)))),
% 0.75/0.94      inference('demod', [status(thm)], ['23', '24'])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X3 @ X4)
% 0.75/0.94          | ~ (r2_hidden @ X3 @ X5)
% 0.75/0.94          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.94          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.75/0.94          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.75/0.94          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | ~ (r2_hidden @ X0 @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['39', '42'])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94               (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94               (k1_tarski @ sk_B)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['38', '43'])).
% 0.75/0.94  thf('45', plain,
% 0.75/0.94      (![X7 : $i, X8 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ X7 @ X8) | (r2_hidden @ (sk_C @ X8 @ X7) @ X7))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         (~ (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ 
% 0.75/0.94             (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.75/0.94      inference('clc', [status(thm)], ['44', '45'])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ sk_A)
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['20', '46'])).
% 0.75/0.94  thf('48', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_B)) @ sk_A))),
% 0.75/0.94      inference('simplify', [status(thm)], ['47'])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r2_hidden @ sk_B @ sk_A)
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.75/0.94          | (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['17', '48'])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ (k1_tarski @ sk_B) @ X0) | (r2_hidden @ sk_B @ sk_A))),
% 0.75/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.75/0.94  thf('51', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf('52', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)),
% 0.75/0.94      inference('clc', [status(thm)], ['50', '51'])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['3', '5'])).
% 0.75/0.94  thf('55', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.94  thf('56', plain,
% 0.75/0.94      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X9 @ X7)
% 0.75/0.94          | ~ (r2_hidden @ X9 @ X10)
% 0.75/0.94          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['55', '56'])).
% 0.75/0.94  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ sk_B @ X0)),
% 0.75/0.94      inference('sup-', [status(thm)], ['52', '57'])).
% 0.75/0.94  thf('59', plain, ($false), inference('sup-', [status(thm)], ['6', '58'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
