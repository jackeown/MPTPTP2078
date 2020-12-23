%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMy343tX6N

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:31 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  167 (2672 expanded)
%              Number of leaves         :   25 ( 871 expanded)
%              Depth                    :   32
%              Number of atoms          : 1465 (24547 expanded)
%              Number of equality atoms :  139 (2541 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( X19 = X20 )
      | ( X19 = X21 )
      | ( X19 = X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ( X3
        = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ X17 )
      | ( ( k4_xboole_0 @ X15 @ X17 )
       != X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('38',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('40',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('53',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('54',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['45','51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('57',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X24 @ X25 @ X26 )
      | ~ ( r2_hidden @ X28 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 )
      | ( ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 )
      | ( ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['45','51','52','53'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('76',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('77',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) )
      = ( k4_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('82',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('83',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('91',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['80','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('100',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('101',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('107',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['104','118'])).

thf('120',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_D @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','121'])).

thf('123',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 @ X2 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','129'])).

thf('131',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','130'])).

thf('132',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('133',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('136',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('139',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZMy343tX6N
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.82/1.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/1.00  % Solved by: fo/fo7.sh
% 0.82/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/1.00  % done 1181 iterations in 0.559s
% 0.82/1.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/1.00  % SZS output start Refutation
% 0.82/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.82/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.82/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.82/1.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.82/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.82/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/1.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.82/1.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.82/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.82/1.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.82/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/1.00  thf(d1_enumset1, axiom,
% 0.82/1.00    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.00     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.00       ( ![E:$i]:
% 0.82/1.00         ( ( r2_hidden @ E @ D ) <=>
% 0.82/1.00           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.82/1.00  thf(zf_stmt_0, axiom,
% 0.82/1.00    (![E:$i,C:$i,B:$i,A:$i]:
% 0.82/1.00     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.82/1.00       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.82/1.00  thf('0', plain,
% 0.82/1.00      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.82/1.00         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.82/1.00          | ((X19) = (X20))
% 0.82/1.00          | ((X19) = (X21))
% 0.82/1.00          | ((X19) = (X22)))),
% 0.82/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.00  thf(d5_xboole_0, axiom,
% 0.82/1.00    (![A:$i,B:$i,C:$i]:
% 0.82/1.00     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.82/1.00       ( ![D:$i]:
% 0.82/1.00         ( ( r2_hidden @ D @ C ) <=>
% 0.82/1.00           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.82/1.00  thf('1', plain,
% 0.82/1.00      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.82/1.00         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.82/1.00          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.82/1.00          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.82/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.00  thf(t48_xboole_1, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.82/1.00  thf('2', plain,
% 0.82/1.00      (![X13 : $i, X14 : $i]:
% 0.82/1.00         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.00           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.00  thf('3', plain,
% 0.82/1.00      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.82/1.00         (~ (r2_hidden @ X6 @ X5)
% 0.82/1.00          | (r2_hidden @ X6 @ X3)
% 0.82/1.00          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.00  thf('4', plain,
% 0.82/1.00      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.82/1.00         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.00      inference('simplify', [status(thm)], ['3'])).
% 0.82/1.00  thf('5', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.00         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.82/1.00      inference('sup-', [status(thm)], ['2', '4'])).
% 0.82/1.00  thf('6', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.82/1.00         ((r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.82/1.00          | ((X3) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))
% 0.82/1.00          | (r2_hidden @ (sk_D @ X3 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.82/1.00      inference('sup-', [status(thm)], ['1', '5'])).
% 0.82/1.00  thf(t47_xboole_1, axiom,
% 0.82/1.00    (![A:$i,B:$i]:
% 0.82/1.00     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.82/1.00  thf('7', plain,
% 0.82/1.00      (![X11 : $i, X12 : $i]:
% 0.82/1.00         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.82/1.00           = (k4_xboole_0 @ X11 @ X12))),
% 0.82/1.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.82/1.00  thf('8', plain,
% 0.82/1.00      (![X13 : $i, X14 : $i]:
% 0.82/1.00         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.00           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.00  thf('9', plain,
% 0.82/1.00      (![X0 : $i, X1 : $i]:
% 0.82/1.00         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.00           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.82/1.00      inference('sup+', [status(thm)], ['7', '8'])).
% 0.82/1.00  thf('10', plain,
% 0.82/1.00      (![X13 : $i, X14 : $i]:
% 0.82/1.00         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.00           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('11', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf(commutativity_k3_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.82/1.01  thf('12', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('13', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf(t83_xboole_1, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.82/1.01  thf('14', plain,
% 0.82/1.01      (![X15 : $i, X17 : $i]:
% 0.82/1.01         ((r1_xboole_0 @ X15 @ X17) | ((k4_xboole_0 @ X15 @ X17) != (X15)))),
% 0.82/1.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.82/1.01  thf('15', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.82/1.01          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['13', '14'])).
% 0.82/1.01  thf('16', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) != (X0))
% 0.82/1.01          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['12', '15'])).
% 0.82/1.01  thf('17', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) != (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.82/1.01             (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['11', '16'])).
% 0.82/1.01  thf('18', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.82/1.01          (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['17'])).
% 0.82/1.01  thf(d7_xboole_0, axiom,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.82/1.01       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.82/1.01  thf('19', plain,
% 0.82/1.01      (![X8 : $i, X9 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.82/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.82/1.01  thf('20', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ 
% 0.82/1.01           (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)) = (k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.82/1.01  thf('21', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('22', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('23', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['21', '22'])).
% 0.82/1.01  thf('24', plain,
% 0.82/1.01      (![X11 : $i, X12 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.82/1.01           = (k4_xboole_0 @ X11 @ X12))),
% 0.82/1.01      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.82/1.01  thf('25', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('26', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['20', '25'])).
% 0.82/1.01  thf('27', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('28', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('29', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['9', '10'])).
% 0.82/1.01  thf('30', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['28', '29'])).
% 0.82/1.01  thf('31', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['27', '30'])).
% 0.82/1.01  thf('32', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('33', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('34', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.82/1.01  thf('35', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) @ 
% 0.82/1.01           k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['26', '34'])).
% 0.82/1.01  thf('36', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['20', '25'])).
% 0.82/1.01  thf('37', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['20', '25'])).
% 0.82/1.01  thf('38', plain,
% 0.82/1.01      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.82/1.01  thf('39', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['20', '25'])).
% 0.82/1.01  thf('40', plain,
% 0.82/1.01      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['38', '39'])).
% 0.82/1.01  thf('41', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X6 @ X5)
% 0.82/1.01          | ~ (r2_hidden @ X6 @ X4)
% 0.82/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('42', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.82/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.82/1.01  thf('43', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['40', '42'])).
% 0.82/1.01  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.82/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.01  thf('45', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((X2) = (k4_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0) @ X1))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X2 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.82/1.01             X2))),
% 0.82/1.01      inference('sup-', [status(thm)], ['6', '44'])).
% 0.82/1.01  thf('46', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.82/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('47', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.82/1.01          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.82/1.01      inference('eq_fact', [status(thm)], ['46'])).
% 0.82/1.01  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.82/1.01      inference('simplify', [status(thm)], ['43'])).
% 0.82/1.01  thf('49', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.01  thf('50', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('51', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['49', '50'])).
% 0.82/1.01  thf('52', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['47', '48'])).
% 0.82/1.01  thf('53', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['49', '50'])).
% 0.82/1.01  thf('54', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i]:
% 0.82/1.01         (((X2) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X2 @ X1 @ k1_xboole_0) @ X2))),
% 0.82/1.01      inference('demod', [status(thm)], ['45', '51', '52', '53'])).
% 0.82/1.01  thf('55', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['2', '4'])).
% 0.82/1.01  thf('56', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.82/1.01             X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['54', '55'])).
% 0.82/1.01  thf(t69_enumset1, axiom,
% 0.82/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.82/1.01  thf('57', plain,
% 0.82/1.01      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.82/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.01  thf(t70_enumset1, axiom,
% 0.82/1.01    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.82/1.01  thf('58', plain,
% 0.82/1.01      (![X31 : $i, X32 : $i]:
% 0.82/1.01         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.82/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.01  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.82/1.01  thf(zf_stmt_2, axiom,
% 0.82/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.82/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.82/1.01       ( ![E:$i]:
% 0.82/1.01         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.82/1.01  thf('59', plain,
% 0.82/1.01      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X28 @ X27)
% 0.82/1.01          | ~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.82/1.01          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.01  thf('60', plain,
% 0.82/1.01      (![X24 : $i, X25 : $i, X26 : $i, X28 : $i]:
% 0.82/1.01         (~ (zip_tseitin_0 @ X28 @ X24 @ X25 @ X26)
% 0.82/1.01          | ~ (r2_hidden @ X28 @ (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['59'])).
% 0.82/1.01  thf('61', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.01          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['58', '60'])).
% 0.82/1.01  thf('62', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.82/1.01          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['57', '61'])).
% 0.82/1.01  thf('63', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.82/1.01          | ~ (zip_tseitin_0 @ 
% 0.82/1.01               (sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0) @ 
% 0.82/1.01               X0 @ X0 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['56', '62'])).
% 0.82/1.01  thf('64', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.82/1.01            = (X0))
% 0.82/1.01          | ((sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.82/1.01              = (X0))
% 0.82/1.01          | ((sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.82/1.01              = (X0))
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['0', '63'])).
% 0.82/1.01  thf('65', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.82/1.01          | ((sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.82/1.01              = (X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['64'])).
% 0.82/1.01  thf('66', plain,
% 0.82/1.01      (![X1 : $i, X2 : $i]:
% 0.82/1.01         (((X2) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X2 @ X1 @ k1_xboole_0) @ X2))),
% 0.82/1.01      inference('demod', [status(thm)], ['45', '51', '52', '53'])).
% 0.82/1.01  thf('67', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('68', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['2', '4'])).
% 0.82/1.01  thf('69', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.82/1.01  thf('70', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.82/1.01             X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['66', '69'])).
% 0.82/1.01  thf('71', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X0 @ X1)
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup+', [status(thm)], ['65', '70'])).
% 0.82/1.01  thf('72', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ X0 @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['71'])).
% 0.82/1.01  thf('73', plain,
% 0.82/1.01      (![X8 : $i, X10 : $i]:
% 0.82/1.01         ((r1_xboole_0 @ X8 @ X10)
% 0.82/1.01          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.82/1.01  thf('74', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k1_xboole_0) != (k1_xboole_0))
% 0.82/1.01          | (r2_hidden @ X1 @ X0)
% 0.82/1.01          | (r1_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['72', '73'])).
% 0.82/1.01  thf('75', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r1_xboole_0 @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 0.82/1.01      inference('simplify', [status(thm)], ['74'])).
% 0.82/1.01  thf(t58_zfmisc_1, conjecture,
% 0.82/1.01    (![A:$i,B:$i]:
% 0.82/1.01     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.82/1.01       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.82/1.01  thf(zf_stmt_3, negated_conjecture,
% 0.82/1.01    (~( ![A:$i,B:$i]:
% 0.82/1.01        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.82/1.01          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.82/1.01    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.82/1.01  thf('76', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.01  thf('77', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.82/1.01      inference('sup-', [status(thm)], ['75', '76'])).
% 0.82/1.01  thf('78', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('79', plain,
% 0.82/1.01      (![X11 : $i, X12 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12))
% 0.82/1.01           = (k4_xboole_0 @ X11 @ X12))),
% 0.82/1.01      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.82/1.01  thf('80', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['78', '79'])).
% 0.82/1.01  thf('81', plain,
% 0.82/1.01      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.82/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.82/1.01  thf('82', plain,
% 0.82/1.01      (![X31 : $i, X32 : $i]:
% 0.82/1.01         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.82/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.82/1.01  thf('83', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.82/1.01         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.82/1.01          | (r2_hidden @ X23 @ X27)
% 0.82/1.01          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.82/1.01  thf('84', plain,
% 0.82/1.01      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.82/1.01         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.82/1.01          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.82/1.01      inference('simplify', [status(thm)], ['83'])).
% 0.82/1.01  thf('85', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.82/1.01          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.82/1.01      inference('sup+', [status(thm)], ['82', '84'])).
% 0.82/1.01  thf('86', plain,
% 0.82/1.01      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.82/1.01         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/1.01  thf('87', plain,
% 0.82/1.01      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.82/1.01         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 0.82/1.01      inference('simplify', [status(thm)], ['86'])).
% 0.82/1.01  thf('88', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['85', '87'])).
% 0.82/1.01  thf('89', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['81', '88'])).
% 0.82/1.01  thf('90', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X2 @ X3)
% 0.82/1.01          | (r2_hidden @ X2 @ X4)
% 0.82/1.01          | (r2_hidden @ X2 @ X5)
% 0.82/1.01          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('91', plain,
% 0.82/1.01      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.82/1.01         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.82/1.01          | (r2_hidden @ X2 @ X4)
% 0.82/1.01          | ~ (r2_hidden @ X2 @ X3))),
% 0.82/1.01      inference('simplify', [status(thm)], ['90'])).
% 0.82/1.01  thf('92', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X0 @ X1)
% 0.82/1.01          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['89', '91'])).
% 0.82/1.01  thf('93', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.82/1.01          | (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 0.82/1.01      inference('sup+', [status(thm)], ['80', '92'])).
% 0.82/1.01  thf('94', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.82/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.82/1.01  thf('95', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 0.82/1.01          | ~ (r2_hidden @ X1 @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['93', '94'])).
% 0.82/1.01  thf('96', plain,
% 0.82/1.01      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['77', '95'])).
% 0.82/1.01  thf('97', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('98', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('99', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ (k1_tarski @ X0) @ X2) = (k1_xboole_0))
% 0.82/1.01          | ((sk_D @ (k3_xboole_0 @ (k1_tarski @ X0) @ X2) @ X1 @ k1_xboole_0)
% 0.82/1.01              = (X0)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['64'])).
% 0.82/1.01  thf('100', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('101', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.82/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('102', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.82/1.01         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.82/1.01          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.82/1.01      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.82/1.01  thf('103', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.82/1.01          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.82/1.01          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['101', '102'])).
% 0.82/1.01  thf('104', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.82/1.01          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.82/1.01      inference('simplify', [status(thm)], ['103'])).
% 0.82/1.01  thf('105', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['49', '50'])).
% 0.82/1.01  thf('106', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('107', plain,
% 0.82/1.01      (![X8 : $i, X10 : $i]:
% 0.82/1.01         ((r1_xboole_0 @ X8 @ X10)
% 0.82/1.01          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.82/1.01      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.82/1.01  thf('108', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('sup-', [status(thm)], ['106', '107'])).
% 0.82/1.01  thf('109', plain,
% 0.82/1.01      (![X0 : $i]:
% 0.82/1.01         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['105', '108'])).
% 0.82/1.01  thf('110', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.82/1.01      inference('simplify', [status(thm)], ['109'])).
% 0.82/1.01  thf('111', plain,
% 0.82/1.01      (![X15 : $i, X16 : $i]:
% 0.82/1.01         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 0.82/1.01      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.82/1.01  thf('112', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.82/1.01  thf('113', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('114', plain,
% 0.82/1.01      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['112', '113'])).
% 0.82/1.01  thf('115', plain,
% 0.82/1.01      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['49', '50'])).
% 0.82/1.01  thf('116', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('117', plain,
% 0.82/1.01      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['115', '116'])).
% 0.82/1.01  thf('118', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.82/1.01      inference('demod', [status(thm)], ['114', '117'])).
% 0.82/1.01  thf('119', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.82/1.01      inference('demod', [status(thm)], ['104', '118'])).
% 0.82/1.01  thf('120', plain,
% 0.82/1.01      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.82/1.01          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['41'])).
% 0.82/1.01  thf('121', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.82/1.01          | ~ (r2_hidden @ (sk_D @ (k4_xboole_0 @ X1 @ X0) @ X2 @ X2) @ X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['119', '120'])).
% 0.82/1.01  thf('122', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ X2) @ 
% 0.82/1.01             (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01          | ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['100', '121'])).
% 0.82/1.01  thf('123', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('124', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/1.01         (~ (r2_hidden @ (sk_D @ (k3_xboole_0 @ X1 @ X0) @ X2 @ X2) @ 
% 0.82/1.01             (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['122', '123'])).
% 0.82/1.01  thf('125', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['99', '124'])).
% 0.82/1.01  thf('126', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.82/1.01          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.82/1.01      inference('simplify', [status(thm)], ['125'])).
% 0.82/1.01  thf('127', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.82/1.01          | ((k3_xboole_0 @ (k1_tarski @ X1) @ 
% 0.82/1.01              (k4_xboole_0 @ (k1_tarski @ X1) @ X0)) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['98', '126'])).
% 0.82/1.01  thf('128', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.82/1.01           = (k4_xboole_0 @ X1 @ X0))),
% 0.82/1.01      inference('sup+', [status(thm)], ['23', '24'])).
% 0.82/1.01  thf('129', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 0.82/1.01          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.82/1.01      inference('demod', [status(thm)], ['127', '128'])).
% 0.82/1.01  thf('130', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]:
% 0.82/1.01         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.82/1.01          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.82/1.01      inference('sup-', [status(thm)], ['97', '129'])).
% 0.82/1.01  thf('131', plain,
% 0.82/1.01      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['96', '130'])).
% 0.82/1.01  thf('132', plain,
% 0.82/1.01      (![X13 : $i, X14 : $i]:
% 0.82/1.01         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.82/1.01           = (k3_xboole_0 @ X13 @ X14))),
% 0.82/1.01      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.82/1.01  thf('133', plain,
% 0.82/1.01      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.82/1.01         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.82/1.01      inference('sup+', [status(thm)], ['131', '132'])).
% 0.82/1.01  thf('134', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.82/1.01      inference('sup-', [status(thm)], ['110', '111'])).
% 0.82/1.01  thf('135', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('136', plain,
% 0.82/1.01      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.82/1.01      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.82/1.01  thf('137', plain,
% 0.82/1.01      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.82/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.82/1.01  thf('138', plain,
% 0.82/1.01      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.82/1.01      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.82/1.01  thf('139', plain,
% 0.82/1.01      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.82/1.01      inference('demod', [status(thm)], ['137', '138'])).
% 0.82/1.01  thf('140', plain, ($false),
% 0.82/1.01      inference('simplify_reflect-', [status(thm)], ['136', '139'])).
% 0.82/1.01  
% 0.82/1.01  % SZS output end Refutation
% 0.82/1.01  
% 0.82/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
