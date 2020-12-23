%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BEDlSFrfO2

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 146 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  884 (1438 expanded)
%              Number of equality atoms :   82 ( 134 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X23 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X19 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X16 @ X17 @ X14 ) ),
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
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( X15 = X16 )
      | ( X15 = X17 )
      | ( X15 = X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_enumset1 @ X27 @ X27 @ X28 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ( X23
       != ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_enumset1 @ X22 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['34','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('63',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['49'])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','60','61','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BEDlSFrfO2
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:32:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.68/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.91  % Solved by: fo/fo7.sh
% 0.68/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.91  % done 532 iterations in 0.448s
% 0.68/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.91  % SZS output start Refutation
% 0.68/0.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.68/0.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.68/0.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.68/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.91  thf(t65_zfmisc_1, conjecture,
% 0.68/0.91    (![A:$i,B:$i]:
% 0.68/0.91     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.68/0.91       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.68/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.91    (~( ![A:$i,B:$i]:
% 0.68/0.91        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.68/0.91          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.68/0.91    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.68/0.91  thf('0', plain,
% 0.68/0.91      (((r2_hidden @ sk_B @ sk_A)
% 0.68/0.91        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.91  thf('1', plain,
% 0.68/0.91      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.68/0.91       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.68/0.91      inference('split', [status(esa)], ['0'])).
% 0.68/0.91  thf(t70_enumset1, axiom,
% 0.68/0.91    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.68/0.91  thf('2', plain,
% 0.68/0.91      (![X27 : $i, X28 : $i]:
% 0.68/0.91         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.68/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.91  thf(d1_enumset1, axiom,
% 0.68/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.91       ( ![E:$i]:
% 0.68/0.91         ( ( r2_hidden @ E @ D ) <=>
% 0.68/0.91           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.68/0.91  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.68/0.91  thf(zf_stmt_2, axiom,
% 0.68/0.91    (![E:$i,C:$i,B:$i,A:$i]:
% 0.68/0.91     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.68/0.91       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.68/0.91  thf(zf_stmt_3, axiom,
% 0.68/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.68/0.91       ( ![E:$i]:
% 0.68/0.91         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.68/0.91  thf('3', plain,
% 0.68/0.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.68/0.91         ((zip_tseitin_0 @ X19 @ X20 @ X21 @ X22)
% 0.68/0.91          | (r2_hidden @ X19 @ X23)
% 0.68/0.91          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.91  thf('4', plain,
% 0.68/0.91      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.68/0.91         ((r2_hidden @ X19 @ (k1_enumset1 @ X22 @ X21 @ X20))
% 0.68/0.91          | (zip_tseitin_0 @ X19 @ X20 @ X21 @ X22))),
% 0.68/0.91      inference('simplify', [status(thm)], ['3'])).
% 0.68/0.91  thf('5', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.68/0.91          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.68/0.91      inference('sup+', [status(thm)], ['2', '4'])).
% 0.68/0.91  thf('6', plain,
% 0.68/0.91      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.91         (((X15) != (X14)) | ~ (zip_tseitin_0 @ X15 @ X16 @ X17 @ X14))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.91  thf('7', plain,
% 0.68/0.91      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.68/0.91         ~ (zip_tseitin_0 @ X14 @ X16 @ X17 @ X14)),
% 0.68/0.91      inference('simplify', [status(thm)], ['6'])).
% 0.68/0.91  thf('8', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.68/0.91      inference('sup-', [status(thm)], ['5', '7'])).
% 0.68/0.91  thf(t69_enumset1, axiom,
% 0.68/0.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.68/0.91  thf('9', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.68/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.91  thf(d5_xboole_0, axiom,
% 0.68/0.91    (![A:$i,B:$i,C:$i]:
% 0.68/0.91     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.68/0.91       ( ![D:$i]:
% 0.68/0.91         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.91           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.68/0.91  thf('10', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.68/0.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.68/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.68/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.91  thf('11', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.68/0.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.68/0.91          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.68/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.68/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.91  thf('12', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.68/0.91          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.68/0.91          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.91  thf('13', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.68/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.91  thf('14', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.68/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.91  thf(l27_zfmisc_1, axiom,
% 0.68/0.91    (![A:$i,B:$i]:
% 0.68/0.91     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.68/0.91  thf('15', plain,
% 0.68/0.91      (![X32 : $i, X33 : $i]:
% 0.68/0.91         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 0.68/0.91      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.68/0.91  thf(d7_xboole_0, axiom,
% 0.68/0.91    (![A:$i,B:$i]:
% 0.68/0.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.68/0.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.68/0.91  thf('16', plain,
% 0.68/0.91      (![X8 : $i, X9 : $i]:
% 0.68/0.91         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.68/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.68/0.91  thf('17', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         ((r2_hidden @ X1 @ X0)
% 0.68/0.91          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['15', '16'])).
% 0.68/0.91  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.91  thf('18', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.91  thf(t100_xboole_1, axiom,
% 0.68/0.91    (![A:$i,B:$i]:
% 0.68/0.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.68/0.91  thf('19', plain,
% 0.68/0.91      (![X11 : $i, X12 : $i]:
% 0.68/0.91         ((k4_xboole_0 @ X11 @ X12)
% 0.68/0.91           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.68/0.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.68/0.91  thf('20', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.68/0.91           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.68/0.91      inference('sup+', [status(thm)], ['18', '19'])).
% 0.68/0.91  thf('21', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.68/0.91            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.68/0.91          | (r2_hidden @ X1 @ X0))),
% 0.68/0.91      inference('sup+', [status(thm)], ['17', '20'])).
% 0.68/0.91  thf(t5_boole, axiom,
% 0.68/0.91    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.68/0.91  thf('22', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.68/0.91      inference('cnf', [status(esa)], [t5_boole])).
% 0.68/0.91  thf('23', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.68/0.91          | (r2_hidden @ X1 @ X0))),
% 0.68/0.91      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.91  thf('24', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X6 @ X5)
% 0.68/0.91          | ~ (r2_hidden @ X6 @ X4)
% 0.68/0.91          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.68/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.91  thf('25', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.68/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.91  thf('26', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X2 @ X0)
% 0.68/0.91          | (r2_hidden @ X1 @ X0)
% 0.68/0.91          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['23', '25'])).
% 0.68/0.91  thf('27', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.91         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.68/0.91          | (r2_hidden @ X0 @ X2)
% 0.68/0.91          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X2))),
% 0.68/0.91      inference('sup-', [status(thm)], ['14', '26'])).
% 0.68/0.91  thf('28', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.68/0.91          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.68/0.91          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['13', '27'])).
% 0.68/0.91  thf('29', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.68/0.91          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['28'])).
% 0.68/0.91  thf('30', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.68/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.91  thf('31', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.68/0.91          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.68/0.91          | ~ (r2_hidden @ X2 @ X1))),
% 0.68/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.68/0.91  thf('32', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.68/0.91          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.68/0.91      inference('condensation', [status(thm)], ['31'])).
% 0.68/0.91  thf('33', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.68/0.91          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['9', '32'])).
% 0.68/0.91  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.68/0.91      inference('sup-', [status(thm)], ['8', '33'])).
% 0.68/0.91  thf('35', plain,
% 0.68/0.91      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.68/0.91      inference('split', [status(esa)], ['0'])).
% 0.68/0.91  thf('36', plain,
% 0.68/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.91         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.68/0.91          | ((X15) = (X16))
% 0.68/0.91          | ((X15) = (X17))
% 0.68/0.91          | ((X15) = (X18)))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.68/0.91  thf('37', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.68/0.91      inference('simplify', [status(thm)], ['12'])).
% 0.68/0.91  thf('38', plain,
% 0.68/0.91      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.68/0.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.68/0.91  thf('39', plain,
% 0.68/0.91      (![X27 : $i, X28 : $i]:
% 0.68/0.91         ((k1_enumset1 @ X27 @ X27 @ X28) = (k2_tarski @ X27 @ X28))),
% 0.68/0.91      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.68/0.91  thf('40', plain,
% 0.68/0.91      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X24 @ X23)
% 0.68/0.91          | ~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.68/0.91          | ((X23) != (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.68/0.91  thf('41', plain,
% 0.68/0.91      (![X20 : $i, X21 : $i, X22 : $i, X24 : $i]:
% 0.68/0.91         (~ (zip_tseitin_0 @ X24 @ X20 @ X21 @ X22)
% 0.68/0.91          | ~ (r2_hidden @ X24 @ (k1_enumset1 @ X22 @ X21 @ X20)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.91  thf('42', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.68/0.91          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.68/0.91      inference('sup-', [status(thm)], ['39', '41'])).
% 0.68/0.91  thf('43', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.68/0.91          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.68/0.91      inference('sup-', [status(thm)], ['38', '42'])).
% 0.68/0.91  thf('44', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.68/0.91          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 0.68/0.91               X0))),
% 0.68/0.91      inference('sup-', [status(thm)], ['37', '43'])).
% 0.68/0.91  thf('45', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.68/0.91          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.68/0.91          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.68/0.91          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['36', '44'])).
% 0.68/0.91  thf('46', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.68/0.91          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['45'])).
% 0.68/0.91  thf('47', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.68/0.91         (((X7) = (k4_xboole_0 @ X3 @ X4))
% 0.68/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.68/0.91          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.68/0.91      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.68/0.91  thf('48', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.68/0.91          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.68/0.91      inference('eq_fact', [status(thm)], ['47'])).
% 0.68/0.91  thf('49', plain,
% 0.68/0.91      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.68/0.91        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.68/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.91  thf('50', plain,
% 0.68/0.91      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('split', [status(esa)], ['49'])).
% 0.68/0.91  thf('51', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.68/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.91  thf('52', plain,
% 0.68/0.91      ((![X0 : $i]:
% 0.68/0.91          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('sup-', [status(thm)], ['50', '51'])).
% 0.68/0.91  thf('53', plain,
% 0.68/0.91      ((![X0 : $i]:
% 0.68/0.91          (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.68/0.91           | ~ (r2_hidden @ 
% 0.68/0.91                (sk_D @ (k1_tarski @ sk_B) @ X0 @ (k1_tarski @ sk_B)) @ sk_A)))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('sup-', [status(thm)], ['48', '52'])).
% 0.68/0.91  thf('54', plain,
% 0.68/0.91      (((~ (r2_hidden @ sk_B @ sk_A)
% 0.68/0.91         | ((k1_tarski @ sk_B)
% 0.68/0.91             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.68/0.91         | ((k1_tarski @ sk_B)
% 0.68/0.91             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('sup-', [status(thm)], ['46', '53'])).
% 0.68/0.91  thf('55', plain,
% 0.68/0.91      (((((k1_tarski @ sk_B)
% 0.68/0.91           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.68/0.91         | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('simplify', [status(thm)], ['54'])).
% 0.68/0.91  thf('56', plain,
% 0.68/0.91      ((((k1_tarski @ sk_B)
% 0.68/0.91          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.68/0.91             ((r2_hidden @ sk_B @ sk_A)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['35', '55'])).
% 0.68/0.91  thf('57', plain,
% 0.68/0.91      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.68/0.91         (~ (r2_hidden @ X6 @ X4)
% 0.68/0.91          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.91  thf('58', plain,
% 0.68/0.91      ((![X0 : $i]:
% 0.68/0.91          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.68/0.91           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.68/0.91             ((r2_hidden @ sk_B @ sk_A)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['56', '57'])).
% 0.68/0.91  thf('59', plain,
% 0.68/0.91      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 0.68/0.91         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.68/0.91             ((r2_hidden @ sk_B @ sk_A)))),
% 0.68/0.91      inference('simplify', [status(thm)], ['58'])).
% 0.68/0.91  thf('60', plain,
% 0.68/0.91      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.68/0.91       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['34', '59'])).
% 0.68/0.91  thf('61', plain,
% 0.68/0.91      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.68/0.91       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.68/0.91      inference('split', [status(esa)], ['49'])).
% 0.68/0.91  thf('62', plain,
% 0.68/0.91      (![X0 : $i, X1 : $i]:
% 0.68/0.91         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.68/0.91          | (r2_hidden @ X1 @ X0))),
% 0.68/0.91      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.91  thf('63', plain,
% 0.68/0.91      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.68/0.91         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('split', [status(esa)], ['0'])).
% 0.68/0.91  thf('64', plain,
% 0.68/0.91      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.68/0.91         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('sup-', [status(thm)], ['62', '63'])).
% 0.68/0.91  thf('65', plain,
% 0.68/0.91      (((r2_hidden @ sk_B @ sk_A))
% 0.68/0.91         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.68/0.91      inference('simplify', [status(thm)], ['64'])).
% 0.68/0.91  thf('66', plain,
% 0.68/0.91      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.68/0.91      inference('split', [status(esa)], ['49'])).
% 0.68/0.91  thf('67', plain,
% 0.68/0.91      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.68/0.91       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.68/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.91  thf('68', plain, ($false),
% 0.68/0.91      inference('sat_resolution*', [status(thm)], ['1', '60', '61', '67'])).
% 0.68/0.91  
% 0.68/0.91  % SZS output end Refutation
% 0.68/0.91  
% 0.68/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
