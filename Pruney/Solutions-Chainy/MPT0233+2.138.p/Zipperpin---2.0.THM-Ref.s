%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdUkn07gtu

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:52 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 116 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   25
%              Number of atoms          :  739 ( 957 expanded)
%              Number of equality atoms :   60 (  83 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 )
      | ( X18 = X19 )
      | ( X18 = X20 )
      | ( X18 = X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('1',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('2',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k1_enumset1 @ X61 @ X63 @ X62 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('3',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X5 ) @ X4 )
      | ( r1_tarski @ ( k1_enumset1 @ X3 @ X2 @ X1 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) @ X3 )
      | ( r1_tarski @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ X4 ) @ X3 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ X3 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ X4 )
      | ( r1_tarski @ ( k2_tarski @ X3 @ X2 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['10','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tarski @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_enumset1 @ sk_C @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_enumset1 @ sk_C @ X0 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['2','35'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_enumset1 @ sk_C @ X0 @ sk_D ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ sk_C @ X0 @ sk_D ) @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ ( k1_enumset1 @ sk_C @ X0 @ sk_D ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X12: $i] :
      ( ( k5_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ sk_C @ X0 @ sk_D @ sk_A )
      = ( k1_enumset1 @ sk_C @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_C @ sk_D @ sk_A )
    = ( k1_enumset1 @ sk_C @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['1','43'])).

thf('45',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( k1_enumset1 @ X61 @ X63 @ X62 )
      = ( k1_enumset1 @ X61 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('46',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('47',plain,
    ( ( k1_enumset1 @ sk_C @ sk_A @ sk_D )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( r2_hidden @ X22 @ X26 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X22 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) )
      | ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ( X26
       != ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X23 @ X24 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_enumset1 @ X25 @ X24 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C )
      | ( X0 = sk_C )
      | ( X0 = sk_D )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C )
      | ( X0 = sk_D )
      | ( X0 = sk_C ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X20 )
      | ~ ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X19 @ X20 @ X17 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( sk_A = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DdUkn07gtu
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.96  % Solved by: fo/fo7.sh
% 0.78/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.96  % done 1293 iterations in 0.518s
% 0.78/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.96  % SZS output start Refutation
% 0.78/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.78/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.78/0.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.78/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.78/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.78/0.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.78/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.96  thf(d1_enumset1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.78/0.96       ( ![E:$i]:
% 0.78/0.96         ( ( r2_hidden @ E @ D ) <=>
% 0.78/0.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.78/0.96  thf(zf_stmt_0, axiom,
% 0.78/0.96    (![E:$i,C:$i,B:$i,A:$i]:
% 0.78/0.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.78/0.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.78/0.96  thf('0', plain,
% 0.78/0.96      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.78/0.96         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21)
% 0.78/0.96          | ((X18) = (X19))
% 0.78/0.96          | ((X18) = (X20))
% 0.78/0.96          | ((X18) = (X21)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf(t71_enumset1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.78/0.96  thf('1', plain,
% 0.78/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.78/0.96           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.78/0.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.78/0.96  thf(t98_enumset1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.78/0.96  thf('2', plain,
% 0.78/0.96      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X61 @ X63 @ X62) = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.78/0.96      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.78/0.96  thf('3', plain,
% 0.78/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.78/0.96           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.78/0.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.78/0.96  thf(t46_enumset1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.96     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.78/0.96       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.78/0.96  thf('4', plain,
% 0.78/0.96      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 0.78/0.96           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.78/0.96  thf(t7_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.78/0.96  thf('5', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.78/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.96  thf('6', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         (r1_tarski @ (k1_enumset1 @ X3 @ X2 @ X1) @ 
% 0.78/0.96          (k2_enumset1 @ X3 @ X2 @ X1 @ X0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['4', '5'])).
% 0.78/0.96  thf('7', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (r1_tarski @ (k1_enumset1 @ X2 @ X2 @ X1) @ 
% 0.78/0.96          (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['3', '6'])).
% 0.78/0.96  thf(t70_enumset1, axiom,
% 0.78/0.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.78/0.96  thf('8', plain,
% 0.78/0.96      (![X34 : $i, X35 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.78/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/0.96  thf('9', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.78/0.96      inference('demod', [status(thm)], ['7', '8'])).
% 0.78/0.96  thf(t28_zfmisc_1, conjecture,
% 0.78/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.96     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.78/0.96          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.78/0.96  thf(zf_stmt_1, negated_conjecture,
% 0.78/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.96        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.78/0.96             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.78/0.96    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.78/0.96  thf('10', plain,
% 0.78/0.96      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.78/0.96  thf('11', plain,
% 0.78/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.78/0.96           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.78/0.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.78/0.96  thf('12', plain,
% 0.78/0.96      (![X34 : $i, X35 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.78/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/0.96  thf('13', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['11', '12'])).
% 0.78/0.96  thf('14', plain,
% 0.78/0.96      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 0.78/0.96           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.78/0.96  thf('15', plain,
% 0.78/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.78/0.96           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.78/0.96      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.78/0.96  thf('16', plain,
% 0.78/0.96      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 0.78/0.96           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.78/0.96  thf('17', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.78/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.96  thf('18', plain,
% 0.78/0.96      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.78/0.96      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.78/0.96  thf(t1_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i]:
% 0.78/0.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.78/0.96       ( r1_tarski @ A @ C ) ))).
% 0.78/0.96  thf('19', plain,
% 0.78/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.78/0.96         (~ (r1_tarski @ X5 @ X6)
% 0.78/0.96          | ~ (r1_tarski @ X6 @ X7)
% 0.78/0.96          | (r1_tarski @ X5 @ X7))),
% 0.78/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.78/0.96  thf('20', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 0.78/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.78/0.96  thf('21', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['17', '20'])).
% 0.78/0.96  thf('22', plain,
% 0.78/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.78/0.96         (~ (r1_tarski @ X5 @ X6)
% 0.78/0.96          | ~ (r1_tarski @ X6 @ X7)
% 0.78/0.96          | (r1_tarski @ X5 @ X7))),
% 0.78/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.78/0.96  thf('23', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.78/0.96         ((r1_tarski @ X2 @ X3)
% 0.78/0.96          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3))),
% 0.78/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.78/0.96  thf('24', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.78/0.96         (~ (r1_tarski @ 
% 0.78/0.96             (k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X5) @ X4)
% 0.78/0.96          | (r1_tarski @ (k1_enumset1 @ X3 @ X2 @ X1) @ X4))),
% 0.78/0.96      inference('sup-', [status(thm)], ['16', '23'])).
% 0.78/0.96  thf('25', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.78/0.96         (~ (r1_tarski @ (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4) @ X3)
% 0.78/0.96          | (r1_tarski @ (k1_enumset1 @ X2 @ X2 @ X1) @ X3))),
% 0.78/0.96      inference('sup-', [status(thm)], ['15', '24'])).
% 0.78/0.96  thf('26', plain,
% 0.78/0.96      (![X34 : $i, X35 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.78/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/0.96  thf('27', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.78/0.96         (~ (r1_tarski @ (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ X4) @ X3)
% 0.78/0.96          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ X3))),
% 0.78/0.96      inference('demod', [status(thm)], ['25', '26'])).
% 0.78/0.96  thf('28', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.78/0.96         (~ (r1_tarski @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ X4)
% 0.78/0.96          | (r1_tarski @ (k2_tarski @ X3 @ X2) @ X4))),
% 0.78/0.96      inference('sup-', [status(thm)], ['14', '27'])).
% 0.78/0.96  thf('29', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.78/0.96          | (r1_tarski @ (k2_tarski @ X1 @ X1) @ X2))),
% 0.78/0.96      inference('sup-', [status(thm)], ['13', '28'])).
% 0.78/0.96  thf(t69_enumset1, axiom,
% 0.78/0.96    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.78/0.96  thf('30', plain,
% 0.78/0.96      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 0.78/0.96      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.78/0.96  thf('31', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.78/0.96          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.78/0.96      inference('demod', [status(thm)], ['29', '30'])).
% 0.78/0.96  thf('32', plain,
% 0.78/0.96      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D))),
% 0.78/0.96      inference('sup-', [status(thm)], ['10', '31'])).
% 0.78/0.96  thf('33', plain,
% 0.78/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.78/0.96         (~ (r1_tarski @ X5 @ X6)
% 0.78/0.96          | ~ (r1_tarski @ X6 @ X7)
% 0.78/0.96          | (r1_tarski @ X5 @ X7))),
% 0.78/0.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.78/0.96  thf('34', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.78/0.96          | ~ (r1_tarski @ (k2_tarski @ sk_C @ sk_D) @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.78/0.96  thf('35', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (r1_tarski @ (k1_tarski @ sk_A) @ (k1_enumset1 @ sk_C @ sk_D @ X0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['9', '34'])).
% 0.78/0.96  thf('36', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (r1_tarski @ (k1_tarski @ sk_A) @ (k1_enumset1 @ sk_C @ X0 @ sk_D))),
% 0.78/0.96      inference('sup+', [status(thm)], ['2', '35'])).
% 0.78/0.96  thf(l32_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.78/0.96  thf('37', plain,
% 0.78/0.96      (![X0 : $i, X2 : $i]:
% 0.78/0.96         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.78/0.96      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.78/0.96  thf('38', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_enumset1 @ sk_C @ X0 @ sk_D))
% 0.78/0.96           = (k1_xboole_0))),
% 0.78/0.96      inference('sup-', [status(thm)], ['36', '37'])).
% 0.78/0.96  thf(t98_xboole_1, axiom,
% 0.78/0.96    (![A:$i,B:$i]:
% 0.78/0.96     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.78/0.96  thf('39', plain,
% 0.78/0.96      (![X15 : $i, X16 : $i]:
% 0.78/0.96         ((k2_xboole_0 @ X15 @ X16)
% 0.78/0.96           = (k5_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.78/0.96  thf('40', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k2_xboole_0 @ (k1_enumset1 @ sk_C @ X0 @ sk_D) @ (k1_tarski @ sk_A))
% 0.78/0.96           = (k5_xboole_0 @ (k1_enumset1 @ sk_C @ X0 @ sk_D) @ k1_xboole_0))),
% 0.78/0.96      inference('sup+', [status(thm)], ['38', '39'])).
% 0.78/0.96  thf('41', plain,
% 0.78/0.96      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.78/0.96         ((k2_enumset1 @ X29 @ X30 @ X31 @ X32)
% 0.78/0.96           = (k2_xboole_0 @ (k1_enumset1 @ X29 @ X30 @ X31) @ (k1_tarski @ X32)))),
% 0.78/0.96      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.78/0.96  thf(t5_boole, axiom,
% 0.78/0.96    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.78/0.96  thf('42', plain, (![X12 : $i]: ((k5_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.78/0.96      inference('cnf', [status(esa)], [t5_boole])).
% 0.78/0.96  thf('43', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((k2_enumset1 @ sk_C @ X0 @ sk_D @ sk_A)
% 0.78/0.96           = (k1_enumset1 @ sk_C @ X0 @ sk_D))),
% 0.78/0.96      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.78/0.96  thf('44', plain,
% 0.78/0.96      (((k1_enumset1 @ sk_C @ sk_D @ sk_A) = (k1_enumset1 @ sk_C @ sk_C @ sk_D))),
% 0.78/0.96      inference('sup+', [status(thm)], ['1', '43'])).
% 0.78/0.96  thf('45', plain,
% 0.78/0.96      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X61 @ X63 @ X62) = (k1_enumset1 @ X61 @ X62 @ X63))),
% 0.78/0.96      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.78/0.96  thf('46', plain,
% 0.78/0.96      (![X34 : $i, X35 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.78/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/0.96  thf('47', plain,
% 0.78/0.96      (((k1_enumset1 @ sk_C @ sk_A @ sk_D) = (k2_tarski @ sk_C @ sk_D))),
% 0.78/0.96      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.78/0.96  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.78/0.96  thf(zf_stmt_3, axiom,
% 0.78/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.78/0.96       ( ![E:$i]:
% 0.78/0.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.78/0.96  thf('48', plain,
% 0.78/0.96      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.78/0.96         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 0.78/0.96          | (r2_hidden @ X22 @ X26)
% 0.78/0.96          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.78/0.96  thf('49', plain,
% 0.78/0.96      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.78/0.96         ((r2_hidden @ X22 @ (k1_enumset1 @ X25 @ X24 @ X23))
% 0.78/0.96          | (zip_tseitin_0 @ X22 @ X23 @ X24 @ X25))),
% 0.78/0.96      inference('simplify', [status(thm)], ['48'])).
% 0.78/0.96  thf('50', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D))
% 0.78/0.96          | (zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C))),
% 0.78/0.96      inference('sup+', [status(thm)], ['47', '49'])).
% 0.78/0.96  thf('51', plain,
% 0.78/0.96      (![X34 : $i, X35 : $i]:
% 0.78/0.96         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.78/0.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.78/0.96  thf('52', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X27 @ X26)
% 0.78/0.96          | ~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.78/0.96          | ((X26) != (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.78/0.96  thf('53', plain,
% 0.78/0.96      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.78/0.96         (~ (zip_tseitin_0 @ X27 @ X23 @ X24 @ X25)
% 0.78/0.96          | ~ (r2_hidden @ X27 @ (k1_enumset1 @ X25 @ X24 @ X23)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['52'])).
% 0.78/0.96  thf('54', plain,
% 0.78/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.96         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.78/0.96          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.78/0.96      inference('sup-', [status(thm)], ['51', '53'])).
% 0.78/0.96  thf('55', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C)
% 0.78/0.96          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C @ sk_C))),
% 0.78/0.96      inference('sup-', [status(thm)], ['50', '54'])).
% 0.78/0.96  thf('56', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         (((X0) = (sk_C))
% 0.78/0.96          | ((X0) = (sk_C))
% 0.78/0.96          | ((X0) = (sk_D))
% 0.78/0.96          | (zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C))),
% 0.78/0.96      inference('sup-', [status(thm)], ['0', '55'])).
% 0.78/0.96  thf('57', plain,
% 0.78/0.96      (![X0 : $i]:
% 0.78/0.96         ((zip_tseitin_0 @ X0 @ sk_D @ sk_A @ sk_C)
% 0.78/0.96          | ((X0) = (sk_D))
% 0.78/0.96          | ((X0) = (sk_C)))),
% 0.78/0.96      inference('simplify', [status(thm)], ['56'])).
% 0.78/0.96  thf('58', plain,
% 0.78/0.96      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.78/0.96         (((X18) != (X20)) | ~ (zip_tseitin_0 @ X18 @ X19 @ X20 @ X17))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.96  thf('59', plain,
% 0.78/0.96      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.78/0.96         ~ (zip_tseitin_0 @ X20 @ X19 @ X20 @ X17)),
% 0.78/0.96      inference('simplify', [status(thm)], ['58'])).
% 0.78/0.96  thf('60', plain, ((((sk_A) = (sk_C)) | ((sk_A) = (sk_D)))),
% 0.78/0.96      inference('sup-', [status(thm)], ['57', '59'])).
% 0.78/0.96  thf('61', plain, (((sk_A) != (sk_D))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.78/0.96  thf('62', plain, (((sk_A) != (sk_C))),
% 0.78/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.78/0.96  thf('63', plain, ($false),
% 0.78/0.96      inference('simplify_reflect-', [status(thm)], ['60', '61', '62'])).
% 0.78/0.96  
% 0.78/0.96  % SZS output end Refutation
% 0.78/0.96  
% 0.78/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
