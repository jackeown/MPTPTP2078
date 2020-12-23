%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t3FNv7X456

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:12 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 190 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :   30
%              Number of atoms          :  800 (1597 expanded)
%              Number of equality atoms :   93 ( 189 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t13_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t13_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 )
      | ( r2_hidden @ X25 @ X29 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X25 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) )
      | ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ~ ( zip_tseitin_0 @ X20 @ X22 @ X23 @ X20 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( X21 = X22 )
      | ( X21 = X23 )
      | ( X21 = X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','28'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ( X29
       != ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X26 @ X27 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_enumset1 @ X28 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 ) @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 )
        = sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['12','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( ( sk_D @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) @ X0 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) )
      | ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_B )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['10','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( sk_B = X0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['1','67'])).

thf('69',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t3FNv7X456
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.19  % Solved by: fo/fo7.sh
% 1.02/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.19  % done 1166 iterations in 0.739s
% 1.02/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.19  % SZS output start Refutation
% 1.02/1.19  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.02/1.19  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.19  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.02/1.19  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.02/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.19  thf(t13_zfmisc_1, conjecture,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.02/1.19         ( k1_tarski @ A ) ) =>
% 1.02/1.19       ( ( A ) = ( B ) ) ))).
% 1.02/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.19    (~( ![A:$i,B:$i]:
% 1.02/1.19        ( ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 1.02/1.19            ( k1_tarski @ A ) ) =>
% 1.02/1.19          ( ( A ) = ( B ) ) ) )),
% 1.02/1.19    inference('cnf.neg', [status(esa)], [t13_zfmisc_1])).
% 1.02/1.19  thf('0', plain, (((sk_A) != (sk_B))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(d1_enumset1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.19     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.19       ( ![E:$i]:
% 1.02/1.19         ( ( r2_hidden @ E @ D ) <=>
% 1.02/1.19           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.02/1.19  thf(zf_stmt_1, axiom,
% 1.02/1.19    (![E:$i,C:$i,B:$i,A:$i]:
% 1.02/1.19     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.02/1.19       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.02/1.19  thf('1', plain,
% 1.02/1.19      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.19         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.02/1.19          | ((X21) = (X22))
% 1.02/1.19          | ((X21) = (X23))
% 1.02/1.19          | ((X21) = (X24)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.02/1.19  thf(t69_enumset1, axiom,
% 1.02/1.19    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.02/1.19  thf('2', plain, (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.02/1.19      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.19  thf(t70_enumset1, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.02/1.19  thf('3', plain,
% 1.02/1.19      (![X33 : $i, X34 : $i]:
% 1.02/1.19         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.02/1.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.19  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.02/1.19  thf(zf_stmt_3, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.19     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.19       ( ![E:$i]:
% 1.02/1.19         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.02/1.19  thf('4', plain,
% 1.02/1.19      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.02/1.19         ((zip_tseitin_0 @ X25 @ X26 @ X27 @ X28)
% 1.02/1.19          | (r2_hidden @ X25 @ X29)
% 1.02/1.19          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.19  thf('5', plain,
% 1.02/1.19      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.02/1.19         ((r2_hidden @ X25 @ (k1_enumset1 @ X28 @ X27 @ X26))
% 1.02/1.19          | (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28))),
% 1.02/1.19      inference('simplify', [status(thm)], ['4'])).
% 1.02/1.19  thf('6', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.19         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.19          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.19      inference('sup+', [status(thm)], ['3', '5'])).
% 1.02/1.19  thf('7', plain,
% 1.02/1.19      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.19         (((X21) != (X20)) | ~ (zip_tseitin_0 @ X21 @ X22 @ X23 @ X20))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.02/1.19  thf('8', plain,
% 1.02/1.19      (![X20 : $i, X22 : $i, X23 : $i]:
% 1.02/1.19         ~ (zip_tseitin_0 @ X20 @ X22 @ X23 @ X20)),
% 1.02/1.19      inference('simplify', [status(thm)], ['7'])).
% 1.02/1.19  thf('9', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.02/1.19      inference('sup-', [status(thm)], ['6', '8'])).
% 1.02/1.19  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['2', '9'])).
% 1.02/1.19  thf('11', plain,
% 1.02/1.19      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.19         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.02/1.19          | ((X21) = (X22))
% 1.02/1.19          | ((X21) = (X23))
% 1.02/1.19          | ((X21) = (X24)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.02/1.19  thf('12', plain,
% 1.02/1.19      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.02/1.19         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.02/1.19          | ((X21) = (X22))
% 1.02/1.19          | ((X21) = (X23))
% 1.02/1.19          | ((X21) = (X24)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.02/1.19  thf(d4_xboole_0, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.02/1.19       ( ![D:$i]:
% 1.02/1.19         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.19           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.02/1.19  thf('13', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.02/1.19         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.02/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.02/1.19          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.02/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.19  thf('14', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.19          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('eq_fact', [status(thm)], ['13'])).
% 1.02/1.19  thf('15', plain,
% 1.02/1.19      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 1.02/1.19         = (k1_tarski @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t98_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.02/1.19  thf('16', plain,
% 1.02/1.19      (![X18 : $i, X19 : $i]:
% 1.02/1.19         ((k2_xboole_0 @ X18 @ X19)
% 1.02/1.19           = (k5_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.02/1.19  thf(t21_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.02/1.19  thf('17', plain,
% 1.02/1.19      (![X10 : $i, X11 : $i]:
% 1.02/1.19         ((k3_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (X10))),
% 1.02/1.19      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.02/1.19  thf(t100_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.19  thf('18', plain,
% 1.02/1.19      (![X8 : $i, X9 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X8 @ X9)
% 1.02/1.19           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.19  thf('19', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 1.02/1.19           = (k5_xboole_0 @ X0 @ X0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['17', '18'])).
% 1.02/1.19  thf(t46_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 1.02/1.19  thf('20', plain,
% 1.02/1.19      (![X12 : $i, X13 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 1.02/1.19      inference('cnf', [status(esa)], [t46_xboole_1])).
% 1.02/1.19  thf('21', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['19', '20'])).
% 1.02/1.19  thf(t91_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.02/1.19       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.02/1.19  thf('22', plain,
% 1.02/1.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.02/1.19         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.02/1.19           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.02/1.19  thf('23', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.02/1.19           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['21', '22'])).
% 1.02/1.19  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['19', '20'])).
% 1.02/1.19  thf('25', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.02/1.19           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['21', '22'])).
% 1.02/1.19  thf('26', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['24', '25'])).
% 1.02/1.19  thf(t5_boole, axiom,
% 1.02/1.19    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.19  thf('27', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.02/1.19      inference('cnf', [status(esa)], [t5_boole])).
% 1.02/1.19  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.02/1.19      inference('demod', [status(thm)], ['26', '27'])).
% 1.02/1.19  thf('29', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('demod', [status(thm)], ['23', '28'])).
% 1.02/1.19  thf('30', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X0 @ X1)
% 1.02/1.19           = (k5_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['16', '29'])).
% 1.02/1.19  thf('31', plain,
% 1.02/1.19      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['15', '30'])).
% 1.02/1.19  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['19', '20'])).
% 1.02/1.19  thf('33', plain,
% 1.02/1.19      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.02/1.19      inference('demod', [status(thm)], ['31', '32'])).
% 1.02/1.19  thf('34', plain,
% 1.02/1.19      (![X8 : $i, X9 : $i]:
% 1.02/1.19         ((k4_xboole_0 @ X8 @ X9)
% 1.02/1.19           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.19  thf('35', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('demod', [status(thm)], ['23', '28'])).
% 1.02/1.19  thf('36', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((k3_xboole_0 @ X1 @ X0)
% 1.02/1.19           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('sup+', [status(thm)], ['34', '35'])).
% 1.02/1.19  thf('37', plain,
% 1.02/1.19      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.02/1.19         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 1.02/1.19      inference('sup+', [status(thm)], ['33', '36'])).
% 1.02/1.19  thf('38', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.02/1.19      inference('cnf', [status(esa)], [t5_boole])).
% 1.02/1.19  thf('39', plain,
% 1.02/1.19      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 1.02/1.19         = (k1_tarski @ sk_B))),
% 1.02/1.19      inference('demod', [status(thm)], ['37', '38'])).
% 1.02/1.19  thf('40', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X6 @ X5)
% 1.02/1.19          | (r2_hidden @ X6 @ X4)
% 1.02/1.19          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.19  thf('41', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.19         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['40'])).
% 1.02/1.19  thf('42', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 1.02/1.19          | (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['39', '41'])).
% 1.02/1.19  thf('43', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | (r2_hidden @ 
% 1.02/1.19             (sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) @ 
% 1.02/1.19             (k1_tarski @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['14', '42'])).
% 1.02/1.19  thf('44', plain,
% 1.02/1.19      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 1.02/1.19      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.19  thf('45', plain,
% 1.02/1.19      (![X33 : $i, X34 : $i]:
% 1.02/1.19         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 1.02/1.19      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.19  thf('46', plain,
% 1.02/1.19      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X30 @ X29)
% 1.02/1.19          | ~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.02/1.19          | ((X29) != (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.19  thf('47', plain,
% 1.02/1.19      (![X26 : $i, X27 : $i, X28 : $i, X30 : $i]:
% 1.02/1.19         (~ (zip_tseitin_0 @ X30 @ X26 @ X27 @ X28)
% 1.02/1.19          | ~ (r2_hidden @ X30 @ (k1_enumset1 @ X28 @ X27 @ X26)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['46'])).
% 1.02/1.19  thf('48', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.19          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.19      inference('sup-', [status(thm)], ['45', '47'])).
% 1.02/1.19  thf('49', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.19          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['44', '48'])).
% 1.02/1.19  thf('50', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | ~ (zip_tseitin_0 @ 
% 1.02/1.19               (sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) @ sk_A @ 
% 1.02/1.19               sk_A @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['43', '49'])).
% 1.02/1.19  thf('51', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) = (sk_A))
% 1.02/1.19          | ((sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) = (sk_A))
% 1.02/1.19          | ((sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) = (sk_A))
% 1.02/1.19          | ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['12', '50'])).
% 1.02/1.19  thf('52', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | ((sk_D @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B) @ X0) = (sk_A)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['51'])).
% 1.02/1.19  thf('53', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.19          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.19      inference('eq_fact', [status(thm)], ['13'])).
% 1.02/1.19  thf('54', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))
% 1.02/1.19          | ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))))),
% 1.02/1.19      inference('sup+', [status(thm)], ['52', '53'])).
% 1.02/1.19  thf('55', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['54'])).
% 1.02/1.19  thf('56', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.19          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['44', '48'])).
% 1.02/1.19  thf('57', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 1.02/1.19      inference('sup-', [status(thm)], ['55', '56'])).
% 1.02/1.19  thf('58', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((sk_A) = (sk_B))
% 1.02/1.19          | ((sk_A) = (sk_B))
% 1.02/1.19          | ((sk_A) = (sk_B))
% 1.02/1.19          | ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['11', '57'])).
% 1.02/1.19  thf('59', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         (((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))
% 1.02/1.19          | ((sk_A) = (sk_B)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['58'])).
% 1.02/1.19  thf('60', plain, (((sk_A) != (sk_B))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('61', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((k1_tarski @ sk_B) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B)))),
% 1.02/1.19      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 1.02/1.19  thf('62', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X6 @ X5)
% 1.02/1.19          | (r2_hidden @ X6 @ X3)
% 1.02/1.19          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.19      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.19  thf('63', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.19         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['62'])).
% 1.02/1.19  thf('64', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_B)) | (r2_hidden @ X1 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['61', '63'])).
% 1.02/1.19  thf('65', plain, (![X0 : $i]: (r2_hidden @ sk_B @ X0)),
% 1.02/1.19      inference('sup-', [status(thm)], ['10', '64'])).
% 1.02/1.19  thf('66', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.19          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['44', '48'])).
% 1.02/1.19  thf('67', plain, (![X0 : $i]: ~ (zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0)),
% 1.02/1.19      inference('sup-', [status(thm)], ['65', '66'])).
% 1.02/1.19  thf('68', plain,
% 1.02/1.19      (![X0 : $i]: (((sk_B) = (X0)) | ((sk_B) = (X0)) | ((sk_B) = (X0)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['1', '67'])).
% 1.02/1.19  thf('69', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 1.02/1.19      inference('simplify', [status(thm)], ['68'])).
% 1.02/1.19  thf('70', plain, (((sk_B) != (sk_B))),
% 1.02/1.19      inference('demod', [status(thm)], ['0', '69'])).
% 1.02/1.19  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 1.02/1.19  
% 1.02/1.19  % SZS output end Refutation
% 1.02/1.19  
% 1.02/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
