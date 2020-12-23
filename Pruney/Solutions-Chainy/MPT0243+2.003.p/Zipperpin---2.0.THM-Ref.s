%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t4GpidHUFy

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:08 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 354 expanded)
%              Number of leaves         :   20 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  817 (3321 expanded)
%              Number of equality atoms :   43 ( 107 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ~ ( r2_hidden @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ~ ( r2_hidden @ sk_B @ sk_C_2 )
    | ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ ( k1_tarski @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_2 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X17 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X17 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_2 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_2 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
   <= ( r2_hidden @ sk_B @ sk_C_2 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C_2 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['26'])).

thf('29',plain,(
    r2_hidden @ sk_B @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','28'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_C_2 ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_enumset1 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_2 @ ( k2_tarski @ X0 @ sk_B ) )
        = X0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('46',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X2 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X0 @ X2 ) )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_2 @ ( k2_tarski @ sk_A @ X0 ) )
        = X0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( ( sk_A = sk_B )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf('56',plain,(
    sk_A = sk_B ),
    inference(clc,[status(thm)],['54','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r1_tarski @ ( k1_tarski @ X34 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference(eq_fact,[status(thm)],['61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X1 @ X1 ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ ( k1_tarski @ X37 ) @ ( k2_tarski @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('69',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X1 @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference(split,[status(esa)],['6'])).

thf('73',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('74',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 )
   <= ( r2_hidden @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['2','12','23','45'])).

thf('76',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_2 ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['25','56','71','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t4GpidHUFy
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 2099 iterations in 0.717s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.97/1.17  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.97/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.17  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.97/1.17  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.97/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.17  thf(t38_zfmisc_1, conjecture,
% 0.97/1.17    (![A:$i,B:$i,C:$i]:
% 0.97/1.17     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.97/1.17       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i,B:$i,C:$i]:
% 0.97/1.17        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.97/1.17          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.97/1.17  thf('0', plain,
% 0.97/1.17      ((~ (r2_hidden @ sk_B @ sk_C_2)
% 0.97/1.17        | ~ (r2_hidden @ sk_A @ sk_C_2)
% 0.97/1.17        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('1', plain,
% 0.97/1.17      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))
% 0.97/1.17         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('2', plain,
% 0.97/1.17      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)) | 
% 0.97/1.17       ~ ((r2_hidden @ sk_B @ sk_C_2)) | ~ ((r2_hidden @ sk_A @ sk_C_2))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf(t12_zfmisc_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.97/1.17  thf('3', plain,
% 0.97/1.17      (![X37 : $i, X38 : $i]:
% 0.97/1.17         (r1_tarski @ (k1_tarski @ X37) @ (k2_tarski @ X37 @ X38))),
% 0.97/1.17      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.97/1.17  thf(l1_zfmisc_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.97/1.17  thf('4', plain,
% 0.97/1.17      (![X34 : $i, X35 : $i]:
% 0.97/1.17         ((r2_hidden @ X34 @ X35) | ~ (r1_tarski @ (k1_tarski @ X34) @ X35))),
% 0.97/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.97/1.17  thf('5', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.97/1.17  thf('6', plain,
% 0.97/1.17      (((r2_hidden @ sk_A @ sk_C_2)
% 0.97/1.17        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('7', plain,
% 0.97/1.17      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))
% 0.97/1.17         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['6'])).
% 0.97/1.17  thf(d3_tarski, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.17  thf('8', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r2_hidden @ X0 @ X2)
% 0.97/1.17          | ~ (r1_tarski @ X1 @ X2))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('9', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r2_hidden @ X0 @ sk_C_2)
% 0.97/1.17           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.97/1.17         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (((r2_hidden @ sk_A @ sk_C_2))
% 0.97/1.17         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['5', '9'])).
% 0.97/1.17  thf('11', plain,
% 0.97/1.17      ((~ (r2_hidden @ sk_A @ sk_C_2)) <= (~ ((r2_hidden @ sk_A @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('12', plain,
% 0.97/1.17      (((r2_hidden @ sk_A @ sk_C_2)) | 
% 0.97/1.17       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('sup-', [status(thm)], ['10', '11'])).
% 0.97/1.17  thf(t70_enumset1, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.97/1.17  thf('13', plain,
% 0.97/1.17      (![X32 : $i, X33 : $i]:
% 0.97/1.17         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.97/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.97/1.17  thf(d1_enumset1, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.97/1.17       ( ![E:$i]:
% 0.97/1.17         ( ( r2_hidden @ E @ D ) <=>
% 0.97/1.17           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.97/1.17  thf(zf_stmt_2, axiom,
% 0.97/1.17    (![E:$i,C:$i,B:$i,A:$i]:
% 0.97/1.17     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.97/1.17       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_3, axiom,
% 0.97/1.17    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.17     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.97/1.17       ( ![E:$i]:
% 0.97/1.17         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.97/1.17         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.97/1.17          | (r2_hidden @ X20 @ X24)
% 0.97/1.17          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.97/1.17         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.97/1.17          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.97/1.17      inference('simplify', [status(thm)], ['14'])).
% 0.97/1.17  thf('16', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.97/1.17          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.97/1.17      inference('sup+', [status(thm)], ['13', '15'])).
% 0.97/1.17  thf('17', plain,
% 0.97/1.17      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.97/1.17         (((X16) != (X17)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.17  thf('18', plain,
% 0.97/1.17      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.97/1.17         ~ (zip_tseitin_0 @ X17 @ X17 @ X18 @ X15)),
% 0.97/1.17      inference('simplify', [status(thm)], ['17'])).
% 0.97/1.17  thf('19', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['16', '18'])).
% 0.97/1.17  thf('20', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r2_hidden @ X0 @ sk_C_2)
% 0.97/1.17           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.97/1.17         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['7', '8'])).
% 0.97/1.17  thf('21', plain,
% 0.97/1.17      (((r2_hidden @ sk_B @ sk_C_2))
% 0.97/1.17         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('22', plain,
% 0.97/1.17      ((~ (r2_hidden @ sk_B @ sk_C_2)) <= (~ ((r2_hidden @ sk_B @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('23', plain,
% 0.97/1.17      (((r2_hidden @ sk_B @ sk_C_2)) | 
% 0.97/1.17       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('sup-', [status(thm)], ['21', '22'])).
% 0.97/1.17  thf('24', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['2', '12', '23'])).
% 0.97/1.17  thf('25', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.97/1.17  thf('26', plain,
% 0.97/1.17      (((r2_hidden @ sk_B @ sk_C_2)
% 0.97/1.17        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('27', plain,
% 0.97/1.17      (((r2_hidden @ sk_B @ sk_C_2)) <= (((r2_hidden @ sk_B @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['26'])).
% 0.97/1.17  thf('28', plain,
% 0.97/1.17      (((r2_hidden @ sk_B @ sk_C_2)) | 
% 0.97/1.17       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('split', [status(esa)], ['26'])).
% 0.97/1.17  thf('29', plain, (((r2_hidden @ sk_B @ sk_C_2))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '28'])).
% 0.97/1.17  thf('30', plain, ((r2_hidden @ sk_B @ sk_C_2)),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.97/1.17  thf('31', plain,
% 0.97/1.17      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.97/1.17         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.97/1.17          | ((X16) = (X17))
% 0.97/1.17          | ((X16) = (X18))
% 0.97/1.17          | ((X16) = (X19)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.17  thf('32', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('33', plain,
% 0.97/1.17      (![X32 : $i, X33 : $i]:
% 0.97/1.17         ((k1_enumset1 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.97/1.17      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.97/1.17  thf('34', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X25 @ X24)
% 0.97/1.17          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.97/1.17          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.97/1.17  thf('35', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.97/1.17         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.97/1.17          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['34'])).
% 0.97/1.17  thf('36', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.97/1.17          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['33', '35'])).
% 0.97/1.17  thf('37', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.97/1.17          | ~ (zip_tseitin_0 @ (sk_C @ X2 @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ 
% 0.97/1.17               X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['32', '36'])).
% 0.97/1.17  thf('38', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ X1) @ X2))),
% 0.97/1.17      inference('sup-', [status(thm)], ['31', '37'])).
% 0.97/1.17  thf('39', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ X2)
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['38'])).
% 0.97/1.17  thf('40', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('41', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['39', '40'])).
% 0.97/1.17  thf('42', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.97/1.17          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.97/1.17          | ~ (r2_hidden @ X0 @ X1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['41'])).
% 0.97/1.17  thf('43', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (((sk_C @ sk_C_2 @ (k2_tarski @ X0 @ sk_B)) = (X0))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('sup-', [status(thm)], ['30', '42'])).
% 0.97/1.17  thf('44', plain,
% 0.97/1.17      (((r2_hidden @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 0.97/1.17      inference('split', [status(esa)], ['6'])).
% 0.97/1.17  thf('45', plain,
% 0.97/1.17      (((r2_hidden @ sk_A @ sk_C_2)) | 
% 0.97/1.17       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('split', [status(esa)], ['6'])).
% 0.97/1.17  thf('46', plain, (((r2_hidden @ sk_A @ sk_C_2))),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '45'])).
% 0.97/1.17  thf('47', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 0.97/1.17  thf('48', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ X2)
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['38'])).
% 0.97/1.17  thf('49', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('50', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | ((sk_C @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ X2) @ X1)
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ X2) @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['48', '49'])).
% 0.97/1.17  thf('51', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X0 @ X2) @ X1)
% 0.97/1.17          | ((sk_C @ X1 @ (k2_tarski @ X0 @ X2)) = (X2))
% 0.97/1.17          | ~ (r2_hidden @ X0 @ X1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['50'])).
% 0.97/1.17  thf('52', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (((sk_C @ sk_C_2 @ (k2_tarski @ sk_A @ X0)) = (X0))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ sk_A @ X0) @ sk_C_2))),
% 0.97/1.17      inference('sup-', [status(thm)], ['47', '51'])).
% 0.97/1.17  thf('53', plain,
% 0.97/1.17      ((((sk_A) = (sk_B))
% 0.97/1.17        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)
% 0.97/1.17        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2))),
% 0.97/1.17      inference('sup+', [status(thm)], ['43', '52'])).
% 0.97/1.17  thf('54', plain,
% 0.97/1.17      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2) | ((sk_A) = (sk_B)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['53'])).
% 0.97/1.17  thf('55', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_2)),
% 0.97/1.17      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.97/1.17  thf('56', plain, (((sk_A) = (sk_B))),
% 0.97/1.17      inference('clc', [status(thm)], ['54', '55'])).
% 0.97/1.17  thf(d10_xboole_0, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.17  thf('57', plain,
% 0.97/1.17      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.17  thf('58', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.97/1.17      inference('simplify', [status(thm)], ['57'])).
% 0.97/1.17  thf('59', plain,
% 0.97/1.17      (![X34 : $i, X35 : $i]:
% 0.97/1.17         ((r2_hidden @ X34 @ X35) | ~ (r1_tarski @ (k1_tarski @ X34) @ X35))),
% 0.97/1.17      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.97/1.17  thf('60', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['58', '59'])).
% 0.97/1.17  thf('61', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ X2)
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['38'])).
% 0.97/1.17  thf('62', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (((X0) != (X1))
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X0)) = (X1))
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.97/1.17      inference('eq_fact', [status(thm)], ['61'])).
% 0.97/1.17  thf('63', plain,
% 0.97/1.17      (![X1 : $i, X2 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X1 @ X1) @ X2)
% 0.97/1.17          | ((sk_C @ X2 @ (k2_tarski @ X1 @ X1)) = (X1)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['62'])).
% 0.97/1.17  thf('64', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('65', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1)
% 0.97/1.17          | (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1))),
% 0.97/1.17      inference('sup-', [status(thm)], ['63', '64'])).
% 0.97/1.17  thf('66', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((r1_tarski @ (k2_tarski @ X0 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.97/1.17      inference('simplify', [status(thm)], ['65'])).
% 0.97/1.17  thf('67', plain,
% 0.97/1.17      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['60', '66'])).
% 0.97/1.17  thf('68', plain,
% 0.97/1.17      (![X37 : $i, X38 : $i]:
% 0.97/1.17         (r1_tarski @ (k1_tarski @ X37) @ (k2_tarski @ X37 @ X38))),
% 0.97/1.17      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.97/1.17  thf('69', plain,
% 0.97/1.17      (![X4 : $i, X6 : $i]:
% 0.97/1.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.97/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.18  thf('70', plain,
% 0.97/1.18      (![X0 : $i, X1 : $i]:
% 0.97/1.18         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.97/1.18          | ((k2_tarski @ X1 @ X0) = (k1_tarski @ X1)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['68', '69'])).
% 0.97/1.18  thf('71', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.97/1.18      inference('sup-', [status(thm)], ['67', '70'])).
% 0.97/1.18  thf('72', plain,
% 0.97/1.18      (((r2_hidden @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 0.97/1.18      inference('split', [status(esa)], ['6'])).
% 0.97/1.18  thf('73', plain,
% 0.97/1.18      (![X34 : $i, X36 : $i]:
% 0.97/1.18         ((r1_tarski @ (k1_tarski @ X34) @ X36) | ~ (r2_hidden @ X34 @ X36))),
% 0.97/1.18      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.97/1.18  thf('74', plain,
% 0.97/1.18      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2))
% 0.97/1.18         <= (((r2_hidden @ sk_A @ sk_C_2)))),
% 0.97/1.18      inference('sup-', [status(thm)], ['72', '73'])).
% 0.97/1.18  thf('75', plain, (((r2_hidden @ sk_A @ sk_C_2))),
% 0.97/1.18      inference('sat_resolution*', [status(thm)], ['2', '12', '23', '45'])).
% 0.97/1.18  thf('76', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_2)),
% 0.97/1.18      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.97/1.18  thf('77', plain, ($false),
% 0.97/1.18      inference('demod', [status(thm)], ['25', '56', '71', '76'])).
% 0.97/1.18  
% 0.97/1.18  % SZS output end Refutation
% 0.97/1.18  
% 0.97/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
