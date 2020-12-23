%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLHbwfpBOV

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:33 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 271 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  783 (2927 expanded)
%              Number of equality atoms :   53 ( 169 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X45: $i,X46: $i] :
      ( ( k1_enumset1 @ X45 @ X45 @ X46 )
      = ( k2_tarski @ X45 @ X46 ) ) ),
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

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X42 )
      | ( X42
       != ( k1_enumset1 @ X41 @ X40 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( r2_hidden @ X38 @ ( k1_enumset1 @ X41 @ X40 @ X39 ) )
      | ( zip_tseitin_0 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X33 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X33 @ X35 @ X36 @ X33 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('28',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( X34 != X35 )
      | ~ ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('29',plain,(
    ! [X33: $i,X35: $i,X36: $i] :
      ~ ( zip_tseitin_0 @ X35 @ X35 @ X36 @ X33 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
        | ~ ( r2_hidden @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_B ) )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','26','36','37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','39'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('42',plain,(
    ! [X72: $i,X73: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X72 @ X73 ) )
      = ( k2_xboole_0 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X72: $i,X73: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X72 @ X73 ) )
      = ( k2_xboole_0 @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('46',plain,(
    ! [X74: $i,X75: $i,X76: $i] :
      ( ( r2_hidden @ X74 @ X75 )
      | ( r1_xboole_0 @ ( k2_tarski @ X74 @ X76 ) @ X75 )
      | ( r2_hidden @ X76 @ X75 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) @ X0 )
        = ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['49','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('58',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','26','36','37'])).

thf('59',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','26'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['40','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gLHbwfpBOV
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:35:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.75/1.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.75/1.96  % Solved by: fo/fo7.sh
% 1.75/1.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.75/1.96  % done 3052 iterations in 1.495s
% 1.75/1.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.75/1.96  % SZS output start Refutation
% 1.75/1.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.75/1.96  thf(sk_A_type, type, sk_A: $i).
% 1.75/1.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.75/1.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.75/1.96  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.75/1.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.75/1.96  thf(sk_B_type, type, sk_B: $i).
% 1.75/1.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.75/1.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.75/1.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.75/1.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.75/1.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.75/1.96  thf(t72_zfmisc_1, conjecture,
% 1.75/1.96    (![A:$i,B:$i,C:$i]:
% 1.75/1.96     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.75/1.96       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 1.75/1.96  thf(zf_stmt_0, negated_conjecture,
% 1.75/1.96    (~( ![A:$i,B:$i,C:$i]:
% 1.75/1.96        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.75/1.96          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 1.75/1.96    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 1.75/1.96  thf('0', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 1.75/1.96        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96            = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.96  thf('1', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 1.75/1.96      inference('split', [status(esa)], ['0'])).
% 1.75/1.96  thf('2', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 1.75/1.96        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96            = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.96  thf('3', plain,
% 1.75/1.96      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('split', [status(esa)], ['2'])).
% 1.75/1.96  thf(t70_enumset1, axiom,
% 1.75/1.96    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.75/1.96  thf('4', plain,
% 1.75/1.96      (![X45 : $i, X46 : $i]:
% 1.75/1.96         ((k1_enumset1 @ X45 @ X45 @ X46) = (k2_tarski @ X45 @ X46))),
% 1.75/1.96      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.75/1.96  thf(d1_enumset1, axiom,
% 1.75/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.75/1.96       ( ![E:$i]:
% 1.75/1.96         ( ( r2_hidden @ E @ D ) <=>
% 1.75/1.96           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.75/1.96  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.75/1.96  thf(zf_stmt_2, axiom,
% 1.75/1.96    (![E:$i,C:$i,B:$i,A:$i]:
% 1.75/1.96     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.75/1.96       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.75/1.96  thf(zf_stmt_3, axiom,
% 1.75/1.96    (![A:$i,B:$i,C:$i,D:$i]:
% 1.75/1.96     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.75/1.96       ( ![E:$i]:
% 1.75/1.96         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.75/1.96  thf('5', plain,
% 1.75/1.96      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.75/1.96         ((zip_tseitin_0 @ X38 @ X39 @ X40 @ X41)
% 1.75/1.96          | (r2_hidden @ X38 @ X42)
% 1.75/1.96          | ((X42) != (k1_enumset1 @ X41 @ X40 @ X39)))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.75/1.96  thf('6', plain,
% 1.75/1.96      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.75/1.96         ((r2_hidden @ X38 @ (k1_enumset1 @ X41 @ X40 @ X39))
% 1.75/1.96          | (zip_tseitin_0 @ X38 @ X39 @ X40 @ X41))),
% 1.75/1.96      inference('simplify', [status(thm)], ['5'])).
% 1.75/1.96  thf('7', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.75/1.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.75/1.96      inference('sup+', [status(thm)], ['4', '6'])).
% 1.75/1.96  thf('8', plain,
% 1.75/1.96      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.75/1.96         (((X34) != (X33)) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X33))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.75/1.96  thf('9', plain,
% 1.75/1.96      (![X33 : $i, X35 : $i, X36 : $i]:
% 1.75/1.96         ~ (zip_tseitin_0 @ X33 @ X35 @ X36 @ X33)),
% 1.75/1.96      inference('simplify', [status(thm)], ['8'])).
% 1.75/1.96  thf('10', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.75/1.96      inference('sup-', [status(thm)], ['7', '9'])).
% 1.75/1.96  thf('11', plain,
% 1.75/1.96      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))))),
% 1.75/1.96      inference('split', [status(esa)], ['2'])).
% 1.75/1.96  thf(t79_xboole_1, axiom,
% 1.75/1.96    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.75/1.96  thf('12', plain,
% 1.75/1.96      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 1.75/1.96      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.75/1.96  thf('13', plain,
% 1.75/1.96      (((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))))),
% 1.75/1.96      inference('sup+', [status(thm)], ['11', '12'])).
% 1.75/1.96  thf(t3_xboole_0, axiom,
% 1.75/1.96    (![A:$i,B:$i]:
% 1.75/1.96     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.75/1.96            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.75/1.96       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.75/1.96            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.75/1.96  thf('14', plain,
% 1.75/1.96      (![X4 : $i, X5 : $i]:
% 1.75/1.96         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.75/1.96  thf('15', plain,
% 1.75/1.96      (![X4 : $i, X5 : $i]:
% 1.75/1.96         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.75/1.96  thf('16', plain,
% 1.75/1.96      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.75/1.96         (~ (r2_hidden @ X6 @ X4)
% 1.75/1.96          | ~ (r2_hidden @ X6 @ X7)
% 1.75/1.96          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.75/1.96  thf('17', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         ((r1_xboole_0 @ X1 @ X0)
% 1.75/1.96          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.75/1.96          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.75/1.96      inference('sup-', [status(thm)], ['15', '16'])).
% 1.75/1.96  thf('18', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         ((r1_xboole_0 @ X0 @ X1)
% 1.75/1.96          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.75/1.96          | (r1_xboole_0 @ X0 @ X1))),
% 1.75/1.96      inference('sup-', [status(thm)], ['14', '17'])).
% 1.75/1.96  thf('19', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.75/1.96      inference('simplify', [status(thm)], ['18'])).
% 1.75/1.96  thf('20', plain,
% 1.75/1.96      (((r1_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))))),
% 1.75/1.96      inference('sup-', [status(thm)], ['13', '19'])).
% 1.75/1.96  thf('21', plain,
% 1.75/1.96      (((r2_hidden @ sk_B @ sk_C_1)
% 1.75/1.96        | (r2_hidden @ sk_A @ sk_C_1)
% 1.75/1.96        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96            != (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.75/1.96  thf('22', plain,
% 1.75/1.96      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 1.75/1.96      inference('split', [status(esa)], ['21'])).
% 1.75/1.96  thf('23', plain,
% 1.75/1.96      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.75/1.96         (~ (r2_hidden @ X6 @ X4)
% 1.75/1.96          | ~ (r2_hidden @ X6 @ X7)
% 1.75/1.96          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.75/1.96  thf('24', plain,
% 1.75/1.96      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 1.75/1.96         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['22', '23'])).
% 1.75/1.96  thf('25', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_A @ (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))) & 
% 1.75/1.96             ((r2_hidden @ sk_A @ sk_C_1)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['20', '24'])).
% 1.75/1.96  thf('26', plain,
% 1.75/1.96      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.75/1.96       ~
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['10', '25'])).
% 1.75/1.96  thf('27', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.75/1.96          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.75/1.96      inference('sup+', [status(thm)], ['4', '6'])).
% 1.75/1.96  thf('28', plain,
% 1.75/1.96      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.75/1.96         (((X34) != (X35)) | ~ (zip_tseitin_0 @ X34 @ X35 @ X36 @ X33))),
% 1.75/1.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.75/1.96  thf('29', plain,
% 1.75/1.96      (![X33 : $i, X35 : $i, X36 : $i]:
% 1.75/1.96         ~ (zip_tseitin_0 @ X35 @ X35 @ X36 @ X33)),
% 1.75/1.96      inference('simplify', [status(thm)], ['28'])).
% 1.75/1.96  thf('30', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.75/1.96      inference('sup-', [status(thm)], ['27', '29'])).
% 1.75/1.96  thf('31', plain,
% 1.75/1.96      (((r1_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))))),
% 1.75/1.96      inference('sup-', [status(thm)], ['13', '19'])).
% 1.75/1.96  thf('32', plain,
% 1.75/1.96      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 1.75/1.96      inference('split', [status(esa)], ['21'])).
% 1.75/1.96  thf('33', plain,
% 1.75/1.96      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.75/1.96         (~ (r2_hidden @ X6 @ X4)
% 1.75/1.96          | ~ (r2_hidden @ X6 @ X7)
% 1.75/1.96          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.75/1.96      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.75/1.96  thf('34', plain,
% 1.75/1.96      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_B @ X0)))
% 1.75/1.96         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['32', '33'])).
% 1.75/1.96  thf('35', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_B @ (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))) & 
% 1.75/1.96             ((r2_hidden @ sk_B @ sk_C_1)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['31', '34'])).
% 1.75/1.96  thf('36', plain,
% 1.75/1.96      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 1.75/1.96       ~
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['30', '35'])).
% 1.75/1.96  thf('37', plain,
% 1.75/1.96      (~
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B))) | 
% 1.75/1.96       ((r2_hidden @ sk_B @ sk_C_1)) | ((r2_hidden @ sk_A @ sk_C_1))),
% 1.75/1.96      inference('split', [status(esa)], ['21'])).
% 1.75/1.96  thf('38', plain,
% 1.75/1.96      (~ ((r2_hidden @ sk_B @ sk_C_1)) | 
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('split', [status(esa)], ['0'])).
% 1.75/1.96  thf('39', plain, (~ ((r2_hidden @ sk_B @ sk_C_1))),
% 1.75/1.96      inference('sat_resolution*', [status(thm)], ['3', '26', '36', '37', '38'])).
% 1.75/1.96  thf('40', plain, (~ (r2_hidden @ sk_B @ sk_C_1)),
% 1.75/1.96      inference('simpl_trail', [status(thm)], ['1', '39'])).
% 1.75/1.96  thf(commutativity_k2_tarski, axiom,
% 1.75/1.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.75/1.96  thf('41', plain,
% 1.75/1.96      (![X31 : $i, X32 : $i]:
% 1.75/1.96         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 1.75/1.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.75/1.96  thf(l51_zfmisc_1, axiom,
% 1.75/1.96    (![A:$i,B:$i]:
% 1.75/1.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.75/1.96  thf('42', plain,
% 1.75/1.96      (![X72 : $i, X73 : $i]:
% 1.75/1.96         ((k3_tarski @ (k2_tarski @ X72 @ X73)) = (k2_xboole_0 @ X72 @ X73))),
% 1.75/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.75/1.96  thf('43', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.75/1.96      inference('sup+', [status(thm)], ['41', '42'])).
% 1.75/1.96  thf('44', plain,
% 1.75/1.96      (![X72 : $i, X73 : $i]:
% 1.75/1.96         ((k3_tarski @ (k2_tarski @ X72 @ X73)) = (k2_xboole_0 @ X72 @ X73))),
% 1.75/1.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.75/1.96  thf('45', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.75/1.96      inference('sup+', [status(thm)], ['43', '44'])).
% 1.75/1.96  thf(t57_zfmisc_1, axiom,
% 1.75/1.96    (![A:$i,B:$i,C:$i]:
% 1.75/1.96     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 1.75/1.96          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 1.75/1.96  thf('46', plain,
% 1.75/1.96      (![X74 : $i, X75 : $i, X76 : $i]:
% 1.75/1.96         ((r2_hidden @ X74 @ X75)
% 1.75/1.96          | (r1_xboole_0 @ (k2_tarski @ X74 @ X76) @ X75)
% 1.75/1.96          | (r2_hidden @ X76 @ X75))),
% 1.75/1.96      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 1.75/1.96  thf(t88_xboole_1, axiom,
% 1.75/1.96    (![A:$i,B:$i]:
% 1.75/1.96     ( ( r1_xboole_0 @ A @ B ) =>
% 1.75/1.96       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 1.75/1.96  thf('47', plain,
% 1.75/1.96      (![X23 : $i, X24 : $i]:
% 1.75/1.96         (((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24) = (X23))
% 1.75/1.96          | ~ (r1_xboole_0 @ X23 @ X24))),
% 1.75/1.96      inference('cnf', [status(esa)], [t88_xboole_1])).
% 1.75/1.96  thf('48', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         ((r2_hidden @ X1 @ X0)
% 1.75/1.96          | (r2_hidden @ X2 @ X0)
% 1.75/1.96          | ((k4_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) @ X0)
% 1.75/1.96              = (k2_tarski @ X2 @ X1)))),
% 1.75/1.96      inference('sup-', [status(thm)], ['46', '47'])).
% 1.75/1.96  thf('49', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         (((k4_xboole_0 @ (k2_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)) @ X2)
% 1.75/1.96            = (k2_tarski @ X1 @ X0))
% 1.75/1.96          | (r2_hidden @ X1 @ X2)
% 1.75/1.96          | (r2_hidden @ X0 @ X2))),
% 1.75/1.96      inference('sup+', [status(thm)], ['45', '48'])).
% 1.75/1.96  thf('50', plain,
% 1.75/1.96      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 1.75/1.96      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.75/1.96  thf('51', plain,
% 1.75/1.96      (![X23 : $i, X24 : $i]:
% 1.75/1.96         (((k4_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ X24) = (X23))
% 1.75/1.96          | ~ (r1_xboole_0 @ X23 @ X24))),
% 1.75/1.96      inference('cnf', [status(esa)], [t88_xboole_1])).
% 1.75/1.96  thf('52', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 1.75/1.96           = (k4_xboole_0 @ X1 @ X0))),
% 1.75/1.96      inference('sup-', [status(thm)], ['50', '51'])).
% 1.75/1.96  thf('53', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.75/1.96      inference('sup+', [status(thm)], ['43', '44'])).
% 1.75/1.96  thf(t39_xboole_1, axiom,
% 1.75/1.96    (![A:$i,B:$i]:
% 1.75/1.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.75/1.96  thf('54', plain,
% 1.75/1.96      (![X13 : $i, X14 : $i]:
% 1.75/1.96         ((k2_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X13))
% 1.75/1.96           = (k2_xboole_0 @ X13 @ X14))),
% 1.75/1.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.75/1.96  thf('55', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i]:
% 1.75/1.96         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.75/1.96           = (k4_xboole_0 @ X1 @ X0))),
% 1.75/1.96      inference('demod', [status(thm)], ['52', '53', '54'])).
% 1.75/1.96  thf('56', plain,
% 1.75/1.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.75/1.96         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2) = (k2_tarski @ X1 @ X0))
% 1.75/1.96          | (r2_hidden @ X1 @ X2)
% 1.75/1.96          | (r2_hidden @ X0 @ X2))),
% 1.75/1.96      inference('demod', [status(thm)], ['49', '55'])).
% 1.75/1.96  thf('57', plain,
% 1.75/1.96      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          != (k2_tarski @ sk_A @ sk_B)))
% 1.75/1.96         <= (~
% 1.75/1.96             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96                = (k2_tarski @ sk_A @ sk_B))))),
% 1.75/1.96      inference('split', [status(esa)], ['21'])).
% 1.75/1.96  thf('58', plain,
% 1.75/1.96      (~
% 1.75/1.96       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96          = (k2_tarski @ sk_A @ sk_B)))),
% 1.75/1.96      inference('sat_resolution*', [status(thm)], ['3', '26', '36', '37'])).
% 1.75/1.96  thf('59', plain,
% 1.75/1.96      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 1.75/1.96         != (k2_tarski @ sk_A @ sk_B))),
% 1.75/1.96      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 1.75/1.96  thf('60', plain,
% 1.75/1.96      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 1.75/1.96        | (r2_hidden @ sk_B @ sk_C_1)
% 1.75/1.96        | (r2_hidden @ sk_A @ sk_C_1))),
% 1.75/1.96      inference('sup-', [status(thm)], ['56', '59'])).
% 1.75/1.96  thf('61', plain,
% 1.75/1.96      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B @ sk_C_1))),
% 1.75/1.96      inference('simplify', [status(thm)], ['60'])).
% 1.75/1.96  thf('62', plain,
% 1.75/1.96      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 1.75/1.96      inference('split', [status(esa)], ['2'])).
% 1.75/1.96  thf('63', plain, (~ ((r2_hidden @ sk_A @ sk_C_1))),
% 1.75/1.96      inference('sat_resolution*', [status(thm)], ['3', '26'])).
% 1.75/1.96  thf('64', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 1.75/1.96      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 1.75/1.96  thf('65', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 1.75/1.96      inference('clc', [status(thm)], ['61', '64'])).
% 1.75/1.96  thf('66', plain, ($false), inference('demod', [status(thm)], ['40', '65'])).
% 1.75/1.96  
% 1.75/1.96  % SZS output end Refutation
% 1.75/1.96  
% 1.75/1.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
