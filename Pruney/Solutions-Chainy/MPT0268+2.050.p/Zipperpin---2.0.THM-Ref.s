%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lOdev8ZhGi

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:59 EST 2020

% Result     : Theorem 5.85s
% Output     : Refutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 330 expanded)
%              Number of leaves         :   25 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          : 1058 (3540 expanded)
%              Number of equality atoms :   78 ( 247 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_enumset1 @ X30 @ X30 @ X31 )
      = ( k2_tarski @ X30 @ X31 ) ) ),
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

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
        | ( r2_hidden @ sk_B @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ( ( k4_xboole_0 @ X14 @ X16 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('49',plain,
    ( ( ( sk_A != sk_A )
      | ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('52',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A )
      = ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
        | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['14','16'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ X0 )
        = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['70','76'])).

thf('81',plain,
    ( ! [X1: $i] :
        ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['37','81'])).

thf('83',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('89',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','82','83','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lOdev8ZhGi
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.85/6.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.85/6.04  % Solved by: fo/fo7.sh
% 5.85/6.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.85/6.04  % done 4237 iterations in 5.578s
% 5.85/6.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.85/6.04  % SZS output start Refutation
% 5.85/6.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.85/6.04  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.85/6.04  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.85/6.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.85/6.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.85/6.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.85/6.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.85/6.04  thf(sk_A_type, type, sk_A: $i).
% 5.85/6.04  thf(sk_B_type, type, sk_B: $i).
% 5.85/6.04  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.85/6.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.85/6.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.85/6.04  thf(t65_zfmisc_1, conjecture,
% 5.85/6.04    (![A:$i,B:$i]:
% 5.85/6.04     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.85/6.04       ( ~( r2_hidden @ B @ A ) ) ))).
% 5.85/6.04  thf(zf_stmt_0, negated_conjecture,
% 5.85/6.04    (~( ![A:$i,B:$i]:
% 5.85/6.04        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 5.85/6.04          ( ~( r2_hidden @ B @ A ) ) ) )),
% 5.85/6.04    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 5.85/6.04  thf('0', plain,
% 5.85/6.04      (((r2_hidden @ sk_B @ sk_A)
% 5.85/6.04        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 5.85/6.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.04  thf('1', plain,
% 5.85/6.04      (((r2_hidden @ sk_B @ sk_A)) | 
% 5.85/6.04       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.85/6.04      inference('split', [status(esa)], ['0'])).
% 5.85/6.04  thf(t70_enumset1, axiom,
% 5.85/6.04    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.85/6.04  thf('2', plain,
% 5.85/6.04      (![X30 : $i, X31 : $i]:
% 5.85/6.04         ((k1_enumset1 @ X30 @ X30 @ X31) = (k2_tarski @ X30 @ X31))),
% 5.85/6.04      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.85/6.04  thf(d1_enumset1, axiom,
% 5.85/6.04    (![A:$i,B:$i,C:$i,D:$i]:
% 5.85/6.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.85/6.04       ( ![E:$i]:
% 5.85/6.04         ( ( r2_hidden @ E @ D ) <=>
% 5.85/6.04           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 5.85/6.04  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.85/6.04  thf(zf_stmt_2, axiom,
% 5.85/6.04    (![E:$i,C:$i,B:$i,A:$i]:
% 5.85/6.04     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 5.85/6.04       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 5.85/6.04  thf(zf_stmt_3, axiom,
% 5.85/6.04    (![A:$i,B:$i,C:$i,D:$i]:
% 5.85/6.04     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 5.85/6.04       ( ![E:$i]:
% 5.85/6.04         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 5.85/6.04  thf('3', plain,
% 5.85/6.04      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 5.85/6.04         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 5.85/6.04          | (r2_hidden @ X22 @ X26)
% 5.85/6.04          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 5.85/6.04      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.85/6.04  thf('4', plain,
% 5.85/6.04      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 5.85/6.04         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 5.85/6.04          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 5.85/6.04      inference('simplify', [status(thm)], ['3'])).
% 5.85/6.04  thf('5', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 5.85/6.04          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 5.85/6.04      inference('sup+', [status(thm)], ['2', '4'])).
% 5.85/6.04  thf('6', plain,
% 5.85/6.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 5.85/6.04         (((X18) != (X17)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 5.85/6.04      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.85/6.04  thf('7', plain,
% 5.85/6.04      (![X17 : $i, X19 : $i, X20 : $i]:
% 5.85/6.04         ~ (zip_tseitin_0 @ X17 @ X19 @ X20 @ X17)),
% 5.85/6.04      inference('simplify', [status(thm)], ['6'])).
% 5.85/6.04  thf('8', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['5', '7'])).
% 5.85/6.04  thf(t69_enumset1, axiom,
% 5.85/6.04    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.85/6.04  thf('9', plain, (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 5.85/6.04      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.85/6.04  thf(d4_xboole_0, axiom,
% 5.85/6.04    (![A:$i,B:$i,C:$i]:
% 5.85/6.04     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 5.85/6.04       ( ![D:$i]:
% 5.85/6.04         ( ( r2_hidden @ D @ C ) <=>
% 5.85/6.04           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 5.85/6.04  thf('10', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.85/6.04         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 5.85/6.04          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.85/6.04          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.85/6.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.85/6.04  thf('11', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.85/6.04      inference('eq_fact', [status(thm)], ['10'])).
% 5.85/6.04  thf('12', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.85/6.04         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 5.85/6.04          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 5.85/6.04          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 5.85/6.04          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.85/6.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.85/6.04  thf('13', plain,
% 5.85/6.04      (![X0 : $i]:
% 5.85/6.04         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 5.85/6.04          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['11', '12'])).
% 5.85/6.04  thf('14', plain,
% 5.85/6.04      (![X0 : $i]:
% 5.85/6.04         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 5.85/6.04      inference('simplify', [status(thm)], ['13'])).
% 5.85/6.04  thf('15', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X5 : $i]:
% 5.85/6.04         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 5.85/6.04          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 5.85/6.04          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 5.85/6.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.85/6.04  thf('16', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.85/6.04      inference('eq_fact', [status(thm)], ['15'])).
% 5.85/6.04  thf('17', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('clc', [status(thm)], ['14', '16'])).
% 5.85/6.04  thf('18', plain,
% 5.85/6.04      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 5.85/6.04      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.85/6.04  thf('19', plain,
% 5.85/6.04      (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 5.85/6.04      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.85/6.04  thf(l27_zfmisc_1, axiom,
% 5.85/6.04    (![A:$i,B:$i]:
% 5.85/6.04     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 5.85/6.04  thf('20', plain,
% 5.85/6.04      (![X39 : $i, X40 : $i]:
% 5.85/6.04         ((r1_xboole_0 @ (k1_tarski @ X39) @ X40) | (r2_hidden @ X39 @ X40))),
% 5.85/6.04      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 5.85/6.04  thf(symmetry_r1_xboole_0, axiom,
% 5.85/6.04    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 5.85/6.04  thf('21', plain,
% 5.85/6.04      (![X6 : $i, X7 : $i]:
% 5.85/6.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 5.85/6.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.85/6.04  thf('22', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['20', '21'])).
% 5.85/6.04  thf(t83_xboole_1, axiom,
% 5.85/6.04    (![A:$i,B:$i]:
% 5.85/6.04     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.85/6.04  thf('23', plain,
% 5.85/6.04      (![X14 : $i, X15 : $i]:
% 5.85/6.04         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 5.85/6.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.85/6.04  thf('24', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ X0 @ X1)
% 5.85/6.04          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['22', '23'])).
% 5.85/6.04  thf(t100_xboole_1, axiom,
% 5.85/6.04    (![A:$i,B:$i]:
% 5.85/6.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.85/6.04  thf('25', plain,
% 5.85/6.04      (![X12 : $i, X13 : $i]:
% 5.85/6.04         ((k4_xboole_0 @ X12 @ X13)
% 5.85/6.04           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.85/6.04  thf(t1_xboole_0, axiom,
% 5.85/6.04    (![A:$i,B:$i,C:$i]:
% 5.85/6.04     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 5.85/6.04       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 5.85/6.04  thf('26', plain,
% 5.85/6.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X8 @ X9)
% 5.85/6.04          | ~ (r2_hidden @ X8 @ X10)
% 5.85/6.04          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.85/6.04  thf('27', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['25', '26'])).
% 5.85/6.04  thf('28', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ X0)
% 5.85/6.04          | (r2_hidden @ X1 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['24', '27'])).
% 5.85/6.04  thf('29', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 5.85/6.04          | (r2_hidden @ X1 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X0))),
% 5.85/6.04      inference('simplify', [status(thm)], ['28'])).
% 5.85/6.04  thf('30', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X1)
% 5.85/6.04          | (r2_hidden @ X0 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['19', '29'])).
% 5.85/6.04  thf('31', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X4 @ X3)
% 5.85/6.04          | (r2_hidden @ X4 @ X1)
% 5.85/6.04          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 5.85/6.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.85/6.04  thf('32', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.85/6.04         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.85/6.04      inference('simplify', [status(thm)], ['31'])).
% 5.85/6.04  thf('33', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         ((r2_hidden @ X0 @ X1)
% 5.85/6.04          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0))))),
% 5.85/6.04      inference('clc', [status(thm)], ['30', '32'])).
% 5.85/6.04  thf('34', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.85/6.04          | (r2_hidden @ X0 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['18', '33'])).
% 5.85/6.04  thf('35', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.85/6.04          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['17', '34'])).
% 5.85/6.04  thf('36', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 5.85/6.04          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['9', '35'])).
% 5.85/6.04  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.85/6.04      inference('sup-', [status(thm)], ['8', '36'])).
% 5.85/6.04  thf('38', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 5.85/6.04      inference('eq_fact', [status(thm)], ['15'])).
% 5.85/6.04  thf('39', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 5.85/6.04          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['17', '34'])).
% 5.85/6.04  thf('40', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.85/6.04          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['38', '39'])).
% 5.85/6.04  thf('41', plain,
% 5.85/6.04      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('split', [status(esa)], ['0'])).
% 5.85/6.04  thf('42', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X0 @ X1)
% 5.85/6.04          | ~ (r2_hidden @ X0 @ X2)
% 5.85/6.04          | (r2_hidden @ X0 @ X3)
% 5.85/6.04          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 5.85/6.04      inference('cnf', [status(esa)], [d4_xboole_0])).
% 5.85/6.04  thf('43', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 5.85/6.04          | ~ (r2_hidden @ X0 @ X2)
% 5.85/6.04          | ~ (r2_hidden @ X0 @ X1))),
% 5.85/6.04      inference('simplify', [status(thm)], ['42'])).
% 5.85/6.04  thf('44', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          (~ (r2_hidden @ sk_B @ X0)
% 5.85/6.04           | (r2_hidden @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))))
% 5.85/6.04         <= (((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['41', '43'])).
% 5.85/6.04  thf('45', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 5.85/6.04           | (r2_hidden @ sk_B @ (k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))))
% 5.85/6.04         <= (((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['40', '44'])).
% 5.85/6.04  thf('46', plain,
% 5.85/6.04      ((~ (r2_hidden @ sk_B @ sk_A)
% 5.85/6.04        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.85/6.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.04  thf('47', plain,
% 5.85/6.04      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('split', [status(esa)], ['46'])).
% 5.85/6.04  thf('48', plain,
% 5.85/6.04      (![X14 : $i, X16 : $i]:
% 5.85/6.04         ((r1_xboole_0 @ X14 @ X16) | ((k4_xboole_0 @ X14 @ X16) != (X14)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.85/6.04  thf('49', plain,
% 5.85/6.04      (((((sk_A) != (sk_A)) | (r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['47', '48'])).
% 5.85/6.04  thf('50', plain,
% 5.85/6.04      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('simplify', [status(thm)], ['49'])).
% 5.85/6.04  thf('51', plain,
% 5.85/6.04      (![X6 : $i, X7 : $i]:
% 5.85/6.04         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 5.85/6.04      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 5.85/6.04  thf('52', plain,
% 5.85/6.04      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['50', '51'])).
% 5.85/6.04  thf('53', plain,
% 5.85/6.04      (![X14 : $i, X15 : $i]:
% 5.85/6.04         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 5.85/6.04      inference('cnf', [status(esa)], [t83_xboole_1])).
% 5.85/6.04  thf('54', plain,
% 5.85/6.04      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A) = (k1_tarski @ sk_B)))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['52', '53'])).
% 5.85/6.04  thf('55', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['25', '26'])).
% 5.85/6.04  thf('56', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 5.85/6.04           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 5.85/6.04           | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['54', '55'])).
% 5.85/6.04  thf('57', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          (~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 5.85/6.04           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('simplify', [status(thm)], ['56'])).
% 5.85/6.04  thf('58', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 5.85/6.04           | ~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 5.85/6.04             ((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['45', '57'])).
% 5.85/6.04  thf('59', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (((k1_tarski @ X0) = (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 5.85/6.04          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['38', '39'])).
% 5.85/6.04  thf('60', plain,
% 5.85/6.04      ((![X0 : $i]:
% 5.85/6.04          ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 5.85/6.04             ((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('clc', [status(thm)], ['58', '59'])).
% 5.85/6.04  thf('61', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 5.85/6.04          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 5.85/6.04      inference('eq_fact', [status(thm)], ['10'])).
% 5.85/6.04  thf('62', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('clc', [status(thm)], ['14', '16'])).
% 5.85/6.04  thf('63', plain,
% 5.85/6.04      (![X12 : $i, X13 : $i]:
% 5.85/6.04         ((k4_xboole_0 @ X12 @ X13)
% 5.85/6.04           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.85/6.04  thf('64', plain,
% 5.85/6.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('sup+', [status(thm)], ['62', '63'])).
% 5.85/6.04  thf('65', plain,
% 5.85/6.04      (![X12 : $i, X13 : $i]:
% 5.85/6.04         ((k4_xboole_0 @ X12 @ X13)
% 5.85/6.04           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.85/6.04  thf('66', plain,
% 5.85/6.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.85/6.04         ((r2_hidden @ X8 @ X9)
% 5.85/6.04          | (r2_hidden @ X8 @ X10)
% 5.85/6.04          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 5.85/6.04      inference('cnf', [status(esa)], [t1_xboole_0])).
% 5.85/6.04  thf('67', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 5.85/6.04          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.85/6.04          | (r2_hidden @ X2 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['65', '66'])).
% 5.85/6.04  thf('68', plain,
% 5.85/6.04      (![X1 : $i, X2 : $i, X4 : $i]:
% 5.85/6.04         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 5.85/6.04      inference('simplify', [status(thm)], ['31'])).
% 5.85/6.04  thf('69', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         ((r2_hidden @ X2 @ X1) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.85/6.04      inference('clc', [status(thm)], ['67', '68'])).
% 5.85/6.04  thf('70', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 5.85/6.04      inference('sup-', [status(thm)], ['64', '69'])).
% 5.85/6.04  thf('71', plain,
% 5.85/6.04      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('sup+', [status(thm)], ['62', '63'])).
% 5.85/6.04  thf('72', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X2 @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['25', '26'])).
% 5.85/6.04  thf('73', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X1 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ X0)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['71', '72'])).
% 5.85/6.04  thf('74', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('clc', [status(thm)], ['14', '16'])).
% 5.85/6.04  thf('75', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 5.85/6.04          | ~ (r2_hidden @ X1 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X1 @ X0))),
% 5.85/6.04      inference('demod', [status(thm)], ['73', '74'])).
% 5.85/6.04  thf('76', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         (~ (r2_hidden @ X1 @ X0)
% 5.85/6.04          | ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)))),
% 5.85/6.04      inference('simplify', [status(thm)], ['75'])).
% 5.85/6.04  thf('77', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('clc', [status(thm)], ['70', '76'])).
% 5.85/6.04  thf('78', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((k5_xboole_0 @ X0 @ X0)
% 5.85/6.04           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X0) @ X1))),
% 5.85/6.04      inference('sup-', [status(thm)], ['61', '77'])).
% 5.85/6.04  thf('79', plain,
% 5.85/6.04      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_tarski @ sk_B)))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 5.85/6.04             ((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('sup+', [status(thm)], ['60', '78'])).
% 5.85/6.04  thf('80', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 5.85/6.04      inference('clc', [status(thm)], ['70', '76'])).
% 5.85/6.04  thf('81', plain,
% 5.85/6.04      ((![X1 : $i]: ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B)))
% 5.85/6.04         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 5.85/6.04             ((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['79', '80'])).
% 5.85/6.04  thf('82', plain,
% 5.85/6.04      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 5.85/6.04       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['37', '81'])).
% 5.85/6.04  thf('83', plain,
% 5.85/6.04      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 5.85/6.04       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.85/6.04      inference('split', [status(esa)], ['46'])).
% 5.85/6.04  thf('84', plain,
% 5.85/6.04      (![X0 : $i, X1 : $i]:
% 5.85/6.04         ((r2_hidden @ X0 @ X1)
% 5.85/6.04          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['22', '23'])).
% 5.85/6.04  thf('85', plain,
% 5.85/6.04      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 5.85/6.04         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('split', [status(esa)], ['0'])).
% 5.85/6.04  thf('86', plain,
% 5.85/6.04      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 5.85/6.04         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('sup-', [status(thm)], ['84', '85'])).
% 5.85/6.04  thf('87', plain,
% 5.85/6.04      (((r2_hidden @ sk_B @ sk_A))
% 5.85/6.04         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 5.85/6.04      inference('simplify', [status(thm)], ['86'])).
% 5.85/6.04  thf('88', plain,
% 5.85/6.04      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 5.85/6.04      inference('split', [status(esa)], ['46'])).
% 5.85/6.04  thf('89', plain,
% 5.85/6.04      (((r2_hidden @ sk_B @ sk_A)) | 
% 5.85/6.04       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 5.85/6.04      inference('sup-', [status(thm)], ['87', '88'])).
% 5.85/6.04  thf('90', plain, ($false),
% 5.85/6.04      inference('sat_resolution*', [status(thm)], ['1', '82', '83', '89'])).
% 5.85/6.04  
% 5.85/6.04  % SZS output end Refutation
% 5.85/6.04  
% 5.85/6.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
