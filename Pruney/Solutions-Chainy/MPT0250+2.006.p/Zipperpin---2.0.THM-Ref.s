%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zM8b8s7sXD

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:48 EST 2020

% Result     : Theorem 2.56s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 199 expanded)
%              Number of leaves         :   32 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  978 (1917 expanded)
%              Number of equality atoms :   62 ( 116 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
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

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('13',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('21',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X55: $i,X56: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X55 @ X56 ) )
      = ( k2_xboole_0 @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B ),
    inference(demod,[status(thm)],['21','26'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r1_xboole_0 @ X20 @ X23 )
      | ~ ( r1_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('54',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['58','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['72','77'])).

thf('82',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('sup-',[status(thm)],['8','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zM8b8s7sXD
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.56/2.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.56/2.75  % Solved by: fo/fo7.sh
% 2.56/2.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.56/2.75  % done 2182 iterations in 2.291s
% 2.56/2.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.56/2.75  % SZS output start Refutation
% 2.56/2.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.56/2.75  thf(sk_B_type, type, sk_B: $i).
% 2.56/2.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.56/2.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.56/2.75  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.56/2.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.56/2.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.56/2.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.56/2.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.56/2.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.56/2.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.56/2.75  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.56/2.75  thf(sk_A_type, type, sk_A: $i).
% 2.56/2.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.56/2.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.56/2.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.56/2.75  thf(t69_enumset1, axiom,
% 2.56/2.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.56/2.75  thf('0', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.56/2.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.56/2.75  thf(t70_enumset1, axiom,
% 2.56/2.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.56/2.75  thf('1', plain,
% 2.56/2.75      (![X41 : $i, X42 : $i]:
% 2.56/2.75         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 2.56/2.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.56/2.75  thf(d1_enumset1, axiom,
% 2.56/2.75    (![A:$i,B:$i,C:$i,D:$i]:
% 2.56/2.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.56/2.75       ( ![E:$i]:
% 2.56/2.75         ( ( r2_hidden @ E @ D ) <=>
% 2.56/2.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.56/2.75  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.56/2.75  thf(zf_stmt_1, axiom,
% 2.56/2.75    (![E:$i,C:$i,B:$i,A:$i]:
% 2.56/2.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.56/2.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.56/2.75  thf(zf_stmt_2, axiom,
% 2.56/2.75    (![A:$i,B:$i,C:$i,D:$i]:
% 2.56/2.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.56/2.75       ( ![E:$i]:
% 2.56/2.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.56/2.75  thf('2', plain,
% 2.56/2.75      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.56/2.75         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 2.56/2.75          | (r2_hidden @ X33 @ X37)
% 2.56/2.75          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.56/2.75  thf('3', plain,
% 2.56/2.75      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.56/2.75         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 2.56/2.75          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 2.56/2.75      inference('simplify', [status(thm)], ['2'])).
% 2.56/2.75  thf('4', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.56/2.75          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.56/2.75      inference('sup+', [status(thm)], ['1', '3'])).
% 2.56/2.75  thf('5', plain,
% 2.56/2.75      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.56/2.75         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.56/2.75  thf('6', plain,
% 2.56/2.75      (![X28 : $i, X30 : $i, X31 : $i]:
% 2.56/2.75         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 2.56/2.75      inference('simplify', [status(thm)], ['5'])).
% 2.56/2.75  thf('7', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['4', '6'])).
% 2.56/2.75  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.56/2.75      inference('sup+', [status(thm)], ['0', '7'])).
% 2.56/2.75  thf('9', plain,
% 2.56/2.75      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.56/2.75         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 2.56/2.75          | ((X29) = (X30))
% 2.56/2.75          | ((X29) = (X31))
% 2.56/2.75          | ((X29) = (X32)))),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.56/2.75  thf(t3_xboole_0, axiom,
% 2.56/2.75    (![A:$i,B:$i]:
% 2.56/2.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.56/2.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.56/2.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.56/2.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.56/2.75  thf('10', plain,
% 2.56/2.75      (![X12 : $i, X13 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf('11', plain,
% 2.56/2.75      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.56/2.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.56/2.75  thf('12', plain,
% 2.56/2.75      (![X41 : $i, X42 : $i]:
% 2.56/2.75         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 2.56/2.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.56/2.75  thf('13', plain,
% 2.56/2.75      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X38 @ X37)
% 2.56/2.75          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 2.56/2.75          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.56/2.75  thf('14', plain,
% 2.56/2.75      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 2.56/2.75         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 2.56/2.75          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 2.56/2.75      inference('simplify', [status(thm)], ['13'])).
% 2.56/2.75  thf('15', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.56/2.75          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['12', '14'])).
% 2.56/2.75  thf('16', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.56/2.75          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 2.56/2.75      inference('sup-', [status(thm)], ['11', '15'])).
% 2.56/2.75  thf('17', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 2.56/2.75          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 2.56/2.75      inference('sup-', [status(thm)], ['10', '16'])).
% 2.56/2.75  thf('18', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.56/2.75          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.56/2.75          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 2.56/2.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['9', '17'])).
% 2.56/2.75  thf('19', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 2.56/2.75          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 2.56/2.75      inference('simplify', [status(thm)], ['18'])).
% 2.56/2.75  thf('20', plain,
% 2.56/2.75      (![X12 : $i, X13 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X13))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf(t45_zfmisc_1, conjecture,
% 2.56/2.75    (![A:$i,B:$i]:
% 2.56/2.75     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.56/2.75       ( r2_hidden @ A @ B ) ))).
% 2.56/2.75  thf(zf_stmt_3, negated_conjecture,
% 2.56/2.75    (~( ![A:$i,B:$i]:
% 2.56/2.75        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 2.56/2.75          ( r2_hidden @ A @ B ) ) )),
% 2.56/2.75    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 2.56/2.75  thf('21', plain,
% 2.56/2.75      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.56/2.75  thf(commutativity_k2_tarski, axiom,
% 2.56/2.75    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.56/2.75  thf('22', plain,
% 2.56/2.75      (![X26 : $i, X27 : $i]:
% 2.56/2.75         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 2.56/2.75      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.56/2.75  thf(l51_zfmisc_1, axiom,
% 2.56/2.75    (![A:$i,B:$i]:
% 2.56/2.75     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.56/2.75  thf('23', plain,
% 2.56/2.75      (![X55 : $i, X56 : $i]:
% 2.56/2.75         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 2.56/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.56/2.75  thf('24', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('sup+', [status(thm)], ['22', '23'])).
% 2.56/2.75  thf('25', plain,
% 2.56/2.75      (![X55 : $i, X56 : $i]:
% 2.56/2.75         ((k3_tarski @ (k2_tarski @ X55 @ X56)) = (k2_xboole_0 @ X55 @ X56))),
% 2.56/2.75      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.56/2.75  thf('26', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('sup+', [status(thm)], ['24', '25'])).
% 2.56/2.75  thf('27', plain,
% 2.56/2.75      ((r1_tarski @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)),
% 2.56/2.75      inference('demod', [status(thm)], ['21', '26'])).
% 2.56/2.75  thf(t28_xboole_1, axiom,
% 2.56/2.75    (![A:$i,B:$i]:
% 2.56/2.75     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.56/2.75  thf('28', plain,
% 2.56/2.75      (![X18 : $i, X19 : $i]:
% 2.56/2.75         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 2.56/2.75      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.56/2.75  thf('29', plain,
% 2.56/2.75      (((k3_xboole_0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ sk_B)
% 2.56/2.75         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['27', '28'])).
% 2.56/2.75  thf(commutativity_k3_xboole_0, axiom,
% 2.56/2.75    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.56/2.75  thf('30', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.56/2.75  thf('31', plain,
% 2.56/2.75      (((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.56/2.75         = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 2.56/2.75      inference('demod', [status(thm)], ['29', '30'])).
% 2.56/2.75  thf('32', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.56/2.75  thf(d4_xboole_0, axiom,
% 2.56/2.75    (![A:$i,B:$i,C:$i]:
% 2.56/2.75     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.56/2.75       ( ![D:$i]:
% 2.56/2.75         ( ( r2_hidden @ D @ C ) <=>
% 2.56/2.75           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.56/2.75  thf('33', plain,
% 2.56/2.75      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X6 @ X5)
% 2.56/2.75          | (r2_hidden @ X6 @ X4)
% 2.56/2.75          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 2.56/2.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.56/2.75  thf('34', plain,
% 2.56/2.75      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.56/2.75         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.56/2.75      inference('simplify', [status(thm)], ['33'])).
% 2.56/2.75  thf('35', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['32', '34'])).
% 2.56/2.75  thf('36', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.56/2.75          | (r2_hidden @ X0 @ sk_B))),
% 2.56/2.75      inference('sup-', [status(thm)], ['31', '35'])).
% 2.56/2.75  thf('37', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.56/2.75          | (r2_hidden @ 
% 2.56/2.75             (sk_C @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ X0) @ sk_B))),
% 2.56/2.75      inference('sup-', [status(thm)], ['20', '36'])).
% 2.56/2.75  thf('38', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((r2_hidden @ X0 @ sk_B)
% 2.56/2.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ 
% 2.56/2.75             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.56/2.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ 
% 2.56/2.75             (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 2.56/2.75      inference('sup+', [status(thm)], ['19', '37'])).
% 2.56/2.75  thf('39', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ (k1_tarski @ X0) @ 
% 2.56/2.75           (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 2.56/2.75          | (r2_hidden @ X0 @ sk_B))),
% 2.56/2.75      inference('simplify', [status(thm)], ['38'])).
% 2.56/2.75  thf(t70_xboole_1, axiom,
% 2.56/2.75    (![A:$i,B:$i,C:$i]:
% 2.56/2.75     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.56/2.75            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.56/2.75       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.56/2.75            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.56/2.75  thf('40', plain,
% 2.56/2.75      (![X20 : $i, X21 : $i, X23 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X20 @ X23)
% 2.56/2.75          | ~ (r1_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X23)))),
% 2.56/2.75      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.56/2.75  thf('41', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((r2_hidden @ X0 @ sk_B)
% 2.56/2.75          | (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ sk_A)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['39', '40'])).
% 2.56/2.75  thf('42', plain,
% 2.56/2.75      (![X12 : $i, X13 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf('43', plain,
% 2.56/2.75      (![X12 : $i, X13 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X12 @ X13) | (r2_hidden @ (sk_C @ X13 @ X12) @ X12))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf('44', plain,
% 2.56/2.75      (![X12 : $i, X14 : $i, X15 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X14 @ X12)
% 2.56/2.75          | ~ (r2_hidden @ X14 @ X15)
% 2.56/2.75          | ~ (r1_xboole_0 @ X12 @ X15))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf('45', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X0 @ X1)
% 2.56/2.75          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.56/2.75          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 2.56/2.75      inference('sup-', [status(thm)], ['43', '44'])).
% 2.56/2.75  thf('46', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r1_xboole_0 @ X0 @ X1)
% 2.56/2.75          | ~ (r1_xboole_0 @ X0 @ X0)
% 2.56/2.75          | (r1_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['42', '45'])).
% 2.56/2.75  thf('47', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.56/2.75      inference('simplify', [status(thm)], ['46'])).
% 2.56/2.75  thf('48', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((r2_hidden @ sk_A @ sk_B) | (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))),
% 2.56/2.75      inference('sup-', [status(thm)], ['41', '47'])).
% 2.56/2.75  thf('49', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 2.56/2.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.56/2.75  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0)),
% 2.56/2.75      inference('clc', [status(thm)], ['48', '49'])).
% 2.56/2.75  thf('51', plain,
% 2.56/2.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.56/2.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 2.56/2.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 2.56/2.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.56/2.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.56/2.75  thf('52', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('eq_fact', [status(thm)], ['51'])).
% 2.56/2.75  thf('53', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('eq_fact', [status(thm)], ['51'])).
% 2.56/2.75  thf('54', plain,
% 2.56/2.75      (![X12 : $i, X14 : $i, X15 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X14 @ X12)
% 2.56/2.75          | ~ (r2_hidden @ X14 @ X15)
% 2.56/2.75          | ~ (r1_xboole_0 @ X12 @ X15))),
% 2.56/2.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.56/2.75  thf('55', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X2))),
% 2.56/2.75      inference('sup-', [status(thm)], ['53', '54'])).
% 2.56/2.75  thf('56', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r1_xboole_0 @ X0 @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['52', '55'])).
% 2.56/2.75  thf('57', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('simplify', [status(thm)], ['56'])).
% 2.56/2.75  thf('58', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         ((k1_tarski @ sk_A) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_A)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['50', '57'])).
% 2.56/2.75  thf('59', plain,
% 2.56/2.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.56/2.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 2.56/2.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 2.56/2.75          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.56/2.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.56/2.75  thf('60', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.56/2.75      inference('eq_fact', [status(thm)], ['59'])).
% 2.56/2.75  thf('61', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 2.56/2.75      inference('eq_fact', [status(thm)], ['59'])).
% 2.56/2.75  thf('62', plain,
% 2.56/2.75      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.56/2.75         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.56/2.75      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.56/2.75  thf('63', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         (((X0) = (k3_xboole_0 @ X0 @ X0))
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 2.56/2.75          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['61', '62'])).
% 2.56/2.75  thf('64', plain,
% 2.56/2.75      (![X0 : $i]:
% 2.56/2.75         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 2.56/2.75      inference('simplify', [status(thm)], ['63'])).
% 2.56/2.75  thf('65', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 2.56/2.75          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('eq_fact', [status(thm)], ['51'])).
% 2.56/2.75  thf('66', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.56/2.75      inference('clc', [status(thm)], ['64', '65'])).
% 2.56/2.75  thf(t100_xboole_1, axiom,
% 2.56/2.75    (![A:$i,B:$i]:
% 2.56/2.75     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.56/2.75  thf('67', plain,
% 2.56/2.75      (![X16 : $i, X17 : $i]:
% 2.56/2.75         ((k4_xboole_0 @ X16 @ X17)
% 2.56/2.75           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 2.56/2.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.56/2.75  thf(t1_xboole_0, axiom,
% 2.56/2.75    (![A:$i,B:$i,C:$i]:
% 2.56/2.75     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 2.56/2.75       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 2.56/2.75  thf('68', plain,
% 2.56/2.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X8 @ X9)
% 2.56/2.75          | ~ (r2_hidden @ X8 @ X10)
% 2.56/2.75          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 2.56/2.75      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.56/2.75  thf('69', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r2_hidden @ X2 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['67', '68'])).
% 2.56/2.75  thf('70', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['32', '34'])).
% 2.56/2.75  thf('71', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('clc', [status(thm)], ['69', '70'])).
% 2.56/2.75  thf('72', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X1 @ X0)
% 2.56/2.75          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 2.56/2.75      inference('sup-', [status(thm)], ['66', '71'])).
% 2.56/2.75  thf('73', plain,
% 2.56/2.75      (![X16 : $i, X17 : $i]:
% 2.56/2.75         ((k4_xboole_0 @ X16 @ X17)
% 2.56/2.75           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 2.56/2.75      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.56/2.75  thf('74', plain,
% 2.56/2.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.56/2.75         ((r2_hidden @ X8 @ X9)
% 2.56/2.75          | (r2_hidden @ X8 @ X10)
% 2.56/2.75          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 2.56/2.75      inference('cnf', [status(esa)], [t1_xboole_0])).
% 2.56/2.75  thf('75', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 2.56/2.75          | (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | (r2_hidden @ X2 @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['73', '74'])).
% 2.56/2.75  thf('76', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.56/2.75          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('clc', [status(thm)], ['69', '70'])).
% 2.56/2.75  thf('77', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.56/2.75         ((r2_hidden @ X2 @ X1) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.56/2.75      inference('clc', [status(thm)], ['75', '76'])).
% 2.56/2.75  thf('78', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.56/2.75      inference('clc', [status(thm)], ['72', '77'])).
% 2.56/2.75  thf('79', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]:
% 2.56/2.75         ((k4_xboole_0 @ X0 @ X0)
% 2.56/2.75           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 2.56/2.75      inference('sup-', [status(thm)], ['60', '78'])).
% 2.56/2.75  thf('80', plain,
% 2.56/2.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_tarski @ sk_A))),
% 2.56/2.75      inference('sup+', [status(thm)], ['58', '79'])).
% 2.56/2.75  thf('81', plain,
% 2.56/2.75      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.56/2.75      inference('clc', [status(thm)], ['72', '77'])).
% 2.56/2.75  thf('82', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ (k1_tarski @ sk_A))),
% 2.56/2.75      inference('sup-', [status(thm)], ['80', '81'])).
% 2.56/2.75  thf('83', plain, ($false), inference('sup-', [status(thm)], ['8', '82'])).
% 2.56/2.75  
% 2.56/2.75  % SZS output end Refutation
% 2.56/2.75  
% 2.56/2.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
