%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kjayajPig6

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:21 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 227 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   23
%              Number of atoms          :  737 (2376 expanded)
%              Number of equality atoms :  112 ( 424 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X58 @ X57 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X57 = k1_xboole_0 )
      | ( X58 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X58 @ X57 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
         != k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X1 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
         != k1_xboole_0 )
        | ( zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,
    ( ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','29'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('31',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('32',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['6','38'])).

thf('40',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('44',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
       != ( k1_tarski @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
         != ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['4','5'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
         != k1_xboole_0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2 )
        | ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
         != k1_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
       != k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kjayajPig6
% 0.13/0.37  % Computer   : n017.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:09:32 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 249 iterations in 0.143s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.62  thf(t130_zfmisc_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62          ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62            ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t130_zfmisc_1])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))
% 0.42/0.62        | ((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf(t113_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X57 : $i, X58 : $i]:
% 0.42/0.62         (((X57) = (k1_xboole_0))
% 0.42/0.62          | ((X58) = (k1_xboole_0))
% 0.42/0.62          | ((k2_zfmisc_1 @ X58 @ X57) != (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))
% 0.42/0.62         | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (((((k1_tarski @ sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.42/0.62  thf('5', plain, (((sk_A) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X57 : $i, X58 : $i]:
% 0.42/0.62         (((X57) = (k1_xboole_0))
% 0.42/0.62          | ((X58) = (k1_xboole_0))
% 0.42/0.62          | ((k2_zfmisc_1 @ X58 @ X57) != (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62         | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.42/0.62         | ((sk_A) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (((((sk_A) = (k1_xboole_0)) | ((k1_tarski @ sk_B) = (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.42/0.62  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf(t69_enumset1, axiom,
% 0.42/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf(t70_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X25 : $i, X26 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf(d1_enumset1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.62       ( ![E:$i]:
% 0.42/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.42/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_2, axiom,
% 0.42/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.42/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_3, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.42/0.62       ( ![E:$i]:
% 0.42/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('15', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.42/0.62          | (r2_hidden @ X17 @ X21)
% 0.42/0.62          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.42/0.62          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.42/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf(l33_zfmisc_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.62       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      (![X52 : $i, X53 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X52 @ X53)
% 0.42/0.62          | ((k4_xboole_0 @ (k1_tarski @ X52) @ X53) != (k1_tarski @ X52)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B))
% 0.42/0.62           | ~ (r2_hidden @ sk_B @ X0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.62  thf(t100_xboole_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X3 : $i, X4 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ X3 @ X4)
% 0.42/0.62           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.42/0.62  thf(commutativity_k5_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.42/0.62  thf(t5_boole, axiom,
% 0.42/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.42/0.62  thf('22', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [t5_boole])).
% 0.42/0.62  thf('23', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['20', '23'])).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (((k3_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.42/0.62           | ~ (r2_hidden @ sk_B @ X0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['19', '24', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62          ((zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2)
% 0.42/0.62           | ((k3_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.42/0.62               != (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '26'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i]:
% 0.42/0.62          (((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 0.42/0.62             != (k1_xboole_0))
% 0.42/0.62           | (zip_tseitin_0 @ sk_B @ X0 @ X1 @ X1)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.42/0.62           | (zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['13', '28'])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62         | (zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '29'])).
% 0.42/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.42/0.62  thf('31', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62         | (zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (((zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['32'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.62         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.42/0.62         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.42/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      (~ (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['33', '35'])).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))) | 
% 0.42/0.62       (((k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('split', [status(esa)], ['0'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['6', '38'])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.42/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      (![X25 : $i, X26 : $i]:
% 0.42/0.62         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.42/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.62         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.42/0.62          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.42/0.62      inference('simplify', [status(thm)], ['15'])).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (![X52 : $i, X53 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X52 @ X53)
% 0.42/0.62          | ((k4_xboole_0 @ (k1_tarski @ X52) @ X53) != (k1_tarski @ X52)))),
% 0.42/0.62      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (((k4_xboole_0 @ k1_xboole_0 @ X0) != (k1_tarski @ sk_B))
% 0.42/0.62           | ~ (r2_hidden @ sk_B @ X0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['20', '23'])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      ((((k1_tarski @ sk_B) = (k1_xboole_0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      ((![X0 : $i]:
% 0.42/0.62          (((k3_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))
% 0.42/0.62           | ~ (r2_hidden @ sk_B @ X0)))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62          ((zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2)
% 0.42/0.62           | ((k3_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.42/0.62               != (k1_xboole_0))))
% 0.42/0.62         <= ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '48'])).
% 0.42/0.62  thf('50', plain,
% 0.42/0.62      ((((k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ sk_B @ X0 @ X1 @ X2)
% 0.42/0.62          | ((k3_xboole_0 @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.42/0.62              != (k1_xboole_0)))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['49', '50'])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k3_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X1 @ X0)) != (k1_xboole_0))
% 0.42/0.62          | (zip_tseitin_0 @ sk_B @ X0 @ X1 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['41', '51'])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.42/0.62          | (zip_tseitin_0 @ sk_B @ X0 @ X0 @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['40', '52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      ((((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | (zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['39', '53'])).
% 0.42/0.62  thf('55', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | (zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['54', '55'])).
% 0.42/0.62  thf('57', plain, ((zip_tseitin_0 @ sk_B @ sk_B @ sk_B @ sk_B)),
% 0.42/0.62      inference('simplify', [status(thm)], ['56'])).
% 0.42/0.62  thf('58', plain,
% 0.42/0.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.42/0.62         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.42/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.62  thf('59', plain, ($false), inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
