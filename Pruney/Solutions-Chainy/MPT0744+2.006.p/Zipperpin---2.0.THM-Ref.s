%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pu228ckZGP

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:00 EST 2020

% Result     : Theorem 3.36s
% Output     : Refutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 236 expanded)
%              Number of leaves         :   37 (  81 expanded)
%              Depth                    :   19
%              Number of atoms          : 1135 (1938 expanded)
%              Number of equality atoms :   54 (  61 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v3_ordinal1 @ X46 )
      | ( r1_ordinal1 @ X47 @ X46 )
      | ( r2_hidden @ X46 @ X47 )
      | ~ ( v3_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('3',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v3_ordinal1 @ X46 )
      | ( r1_ordinal1 @ X47 @ X46 )
      | ( r2_hidden @ X46 @ X47 )
      | ~ ( v3_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('12',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ ( k3_tarski @ X22 ) )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('19',plain,(
    ! [X23: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( r1_tarski @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('22',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('29',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ( r2_hidden @ X45 @ X44 )
      | ~ ( r2_xboole_0 @ X45 @ X44 )
      | ~ ( v1_ordinal1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('31',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('33',plain,(
    ! [X40: $i] :
      ( ( v1_ordinal1 @ X40 )
      | ~ ( v3_ordinal1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('34',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('38',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( sk_A = sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['10'])).

thf('50',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_enumset1 @ X12 @ X12 @ X13 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k2_enumset1 @ X14 @ X14 @ X15 @ X16 )
      = ( k1_enumset1 @ X14 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(d3_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( ( G != E )
              & ( G != D )
              & ( G != C )
              & ( G != B )
              & ( G != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,E: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A )
    <=> ( ( G != A )
        & ( G != B )
        & ( G != C )
        & ( G != D )
        & ( G != E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( F
        = ( k3_enumset1 @ A @ B @ C @ D @ E ) )
    <=> ! [G: $i] :
          ( ( r2_hidden @ G @ F )
        <=> ~ ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) )).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X31 @ X37 )
      | ( X37
       != ( k3_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X31 @ ( k3_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 != X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    ! [X24: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X24 @ X26 @ X27 @ X28 @ X29 @ X24 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_enumset1 @ X0 @ X1 @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X2 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','66'])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( k2_tarski @ X11 @ X11 )
      = ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('69',plain,(
    ! [X41: $i] :
      ( ( k1_ordinal1 @ X41 )
      = ( k2_xboole_0 @ X41 @ ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v3_ordinal1 @ X46 )
      | ( r1_ordinal1 @ X47 @ X46 )
      | ( r2_hidden @ X46 @ X47 )
      | ~ ( v3_ordinal1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('72',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('73',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('81',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('82',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('87',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_xboole_0 @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ( r2_hidden @ X45 @ X44 )
      | ~ ( r2_xboole_0 @ X45 @ X44 )
      | ~ ( v1_ordinal1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('89',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( v1_ordinal1 @ sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X40: $i] :
      ( ( v1_ordinal1 @ X40 )
      | ~ ( v3_ordinal1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('92',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('96',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v3_ordinal1 @ X42 )
      | ~ ( v3_ordinal1 @ X43 )
      | ( r1_tarski @ X42 @ X43 )
      | ~ ( r1_ordinal1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('97',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r2_xboole_0 @ X8 @ X10 )
      | ( X8 = X10 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('102',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v3_ordinal1 @ X44 )
      | ( r2_hidden @ X45 @ X44 )
      | ~ ( r2_xboole_0 @ X45 @ X44 )
      | ~ ( v1_ordinal1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('104',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('106',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('109',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( sk_B = sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','109'])).

thf('111',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('113',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','113'])).

thf('115',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','48','49','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pu228ckZGP
% 0.10/0.31  % Computer   : n016.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 14:13:19 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.31  % Number of cores: 8
% 0.16/0.31  % Python version: Python 3.6.8
% 0.16/0.32  % Running in FO mode
% 3.36/3.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.36/3.57  % Solved by: fo/fo7.sh
% 3.36/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.36/3.57  % done 2831 iterations in 3.133s
% 3.36/3.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.36/3.57  % SZS output start Refutation
% 3.36/3.57  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 3.36/3.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.36/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.36/3.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.36/3.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.36/3.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.36/3.57  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 3.36/3.57  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 3.36/3.57  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 3.36/3.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.36/3.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o).
% 3.36/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.36/3.57  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 3.36/3.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.36/3.57  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 3.36/3.57  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 3.36/3.57  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 3.36/3.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.36/3.57  thf(t34_ordinal1, conjecture,
% 3.36/3.57    (![A:$i]:
% 3.36/3.57     ( ( v3_ordinal1 @ A ) =>
% 3.36/3.57       ( ![B:$i]:
% 3.36/3.57         ( ( v3_ordinal1 @ B ) =>
% 3.36/3.57           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 3.36/3.57             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 3.36/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.36/3.57    (~( ![A:$i]:
% 3.36/3.57        ( ( v3_ordinal1 @ A ) =>
% 3.36/3.57          ( ![B:$i]:
% 3.36/3.57            ( ( v3_ordinal1 @ B ) =>
% 3.36/3.57              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 3.36/3.57                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 3.36/3.57    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 3.36/3.57  thf('0', plain,
% 3.36/3.57      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 3.36/3.57        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('1', plain,
% 3.36/3.57      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 3.36/3.57       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf(t26_ordinal1, axiom,
% 3.36/3.57    (![A:$i]:
% 3.36/3.57     ( ( v3_ordinal1 @ A ) =>
% 3.36/3.57       ( ![B:$i]:
% 3.36/3.57         ( ( v3_ordinal1 @ B ) =>
% 3.36/3.57           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 3.36/3.57  thf('2', plain,
% 3.36/3.57      (![X46 : $i, X47 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X46)
% 3.36/3.57          | (r1_ordinal1 @ X47 @ X46)
% 3.36/3.57          | (r2_hidden @ X46 @ X47)
% 3.36/3.57          | ~ (v3_ordinal1 @ X47))),
% 3.36/3.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 3.36/3.57  thf('3', plain,
% 3.36/3.57      (![X46 : $i, X47 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X46)
% 3.36/3.57          | (r1_ordinal1 @ X47 @ X46)
% 3.36/3.57          | (r2_hidden @ X46 @ X47)
% 3.36/3.57          | ~ (v3_ordinal1 @ X47))),
% 3.36/3.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 3.36/3.57  thf(antisymmetry_r2_hidden, axiom,
% 3.36/3.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 3.36/3.57  thf('4', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 3.36/3.57      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 3.36/3.57  thf('5', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | ~ (r2_hidden @ X0 @ X1))),
% 3.36/3.57      inference('sup-', [status(thm)], ['3', '4'])).
% 3.36/3.57  thf('6', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X1 @ X0)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1))),
% 3.36/3.57      inference('sup-', [status(thm)], ['2', '5'])).
% 3.36/3.57  thf('7', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         ((r1_ordinal1 @ X1 @ X0)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X0))),
% 3.36/3.57      inference('simplify', [status(thm)], ['6'])).
% 3.36/3.57  thf('8', plain,
% 3.36/3.57      (![X0 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 3.36/3.57      inference('eq_fact', [status(thm)], ['7'])).
% 3.36/3.57  thf('9', plain,
% 3.36/3.57      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 3.36/3.57      inference('simplify', [status(thm)], ['8'])).
% 3.36/3.57  thf('10', plain,
% 3.36/3.57      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('11', plain,
% 3.36/3.57      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('split', [status(esa)], ['10'])).
% 3.36/3.57  thf(d1_ordinal1, axiom,
% 3.36/3.57    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 3.36/3.57  thf('12', plain,
% 3.36/3.57      (![X41 : $i]:
% 3.36/3.57         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 3.36/3.57  thf(d3_xboole_0, axiom,
% 3.36/3.57    (![A:$i,B:$i,C:$i]:
% 3.36/3.57     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 3.36/3.57       ( ![D:$i]:
% 3.36/3.57         ( ( r2_hidden @ D @ C ) <=>
% 3.36/3.57           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.36/3.57  thf('13', plain,
% 3.36/3.57      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 3.36/3.57         (~ (r2_hidden @ X6 @ X4)
% 3.36/3.57          | (r2_hidden @ X6 @ X5)
% 3.36/3.57          | (r2_hidden @ X6 @ X3)
% 3.36/3.57          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.36/3.57  thf('14', plain,
% 3.36/3.57      (![X3 : $i, X5 : $i, X6 : $i]:
% 3.36/3.57         ((r2_hidden @ X6 @ X3)
% 3.36/3.57          | (r2_hidden @ X6 @ X5)
% 3.36/3.57          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 3.36/3.57      inference('simplify', [status(thm)], ['13'])).
% 3.36/3.57  thf('15', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 3.36/3.57          | (r2_hidden @ X1 @ X0)
% 3.36/3.57          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['12', '14'])).
% 3.36/3.57  thf('16', plain,
% 3.36/3.57      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['11', '15'])).
% 3.36/3.57  thf(l49_zfmisc_1, axiom,
% 3.36/3.57    (![A:$i,B:$i]:
% 3.36/3.57     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 3.36/3.57  thf('17', plain,
% 3.36/3.57      (![X21 : $i, X22 : $i]:
% 3.36/3.57         ((r1_tarski @ X21 @ (k3_tarski @ X22)) | ~ (r2_hidden @ X21 @ X22))),
% 3.36/3.57      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 3.36/3.57  thf('18', plain,
% 3.36/3.57      ((((r2_hidden @ sk_A @ sk_B)
% 3.36/3.57         | (r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['16', '17'])).
% 3.36/3.57  thf(t31_zfmisc_1, axiom,
% 3.36/3.57    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 3.36/3.57  thf('19', plain, (![X23 : $i]: ((k3_tarski @ (k1_tarski @ X23)) = (X23))),
% 3.36/3.57      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 3.36/3.57  thf('20', plain,
% 3.36/3.57      ((((r2_hidden @ sk_A @ sk_B) | (r1_tarski @ sk_A @ sk_B)))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['18', '19'])).
% 3.36/3.57  thf('21', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | ~ (r2_hidden @ X0 @ X1))),
% 3.36/3.57      inference('sup-', [status(thm)], ['3', '4'])).
% 3.36/3.57  thf('22', plain,
% 3.36/3.57      ((((r1_tarski @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B)
% 3.36/3.57         | (r1_ordinal1 @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A)))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['20', '21'])).
% 3.36/3.57  thf('23', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('25', plain,
% 3.36/3.57      ((((r1_tarski @ sk_A @ sk_B) | (r1_ordinal1 @ sk_A @ sk_B)))
% 3.36/3.57         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['22', '23', '24'])).
% 3.36/3.57  thf('26', plain,
% 3.36/3.57      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf('27', plain,
% 3.36/3.57      (((r1_tarski @ sk_A @ sk_B))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['25', '26'])).
% 3.36/3.57  thf(d8_xboole_0, axiom,
% 3.36/3.57    (![A:$i,B:$i]:
% 3.36/3.57     ( ( r2_xboole_0 @ A @ B ) <=>
% 3.36/3.57       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 3.36/3.57  thf('28', plain,
% 3.36/3.57      (![X8 : $i, X10 : $i]:
% 3.36/3.57         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.36/3.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 3.36/3.57  thf('29', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['27', '28'])).
% 3.36/3.57  thf(t21_ordinal1, axiom,
% 3.36/3.57    (![A:$i]:
% 3.36/3.57     ( ( v1_ordinal1 @ A ) =>
% 3.36/3.57       ( ![B:$i]:
% 3.36/3.57         ( ( v3_ordinal1 @ B ) =>
% 3.36/3.57           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 3.36/3.57  thf('30', plain,
% 3.36/3.57      (![X44 : $i, X45 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X44)
% 3.36/3.57          | (r2_hidden @ X45 @ X44)
% 3.36/3.57          | ~ (r2_xboole_0 @ X45 @ X44)
% 3.36/3.57          | ~ (v1_ordinal1 @ X45))),
% 3.36/3.57      inference('cnf', [status(esa)], [t21_ordinal1])).
% 3.36/3.57  thf('31', plain,
% 3.36/3.57      (((((sk_A) = (sk_B))
% 3.36/3.57         | ~ (v1_ordinal1 @ sk_A)
% 3.36/3.57         | (r2_hidden @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['29', '30'])).
% 3.36/3.57  thf('32', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf(cc1_ordinal1, axiom,
% 3.36/3.57    (![A:$i]:
% 3.36/3.57     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 3.36/3.57  thf('33', plain,
% 3.36/3.57      (![X40 : $i]: ((v1_ordinal1 @ X40) | ~ (v3_ordinal1 @ X40))),
% 3.36/3.57      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 3.36/3.57  thf('34', plain, ((v1_ordinal1 @ sk_A)),
% 3.36/3.57      inference('sup-', [status(thm)], ['32', '33'])).
% 3.36/3.57  thf('35', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('36', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['31', '34', '35'])).
% 3.36/3.57  thf('37', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | ~ (r2_hidden @ X0 @ X1))),
% 3.36/3.57      inference('sup-', [status(thm)], ['3', '4'])).
% 3.36/3.57  thf('38', plain,
% 3.36/3.57      (((((sk_A) = (sk_B))
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B)
% 3.36/3.57         | (r1_ordinal1 @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['36', '37'])).
% 3.36/3.57  thf('39', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('41', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 3.36/3.57  thf('42', plain,
% 3.36/3.57      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf('43', plain,
% 3.36/3.57      ((((sk_A) = (sk_B)))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('clc', [status(thm)], ['41', '42'])).
% 3.36/3.57  thf('44', plain,
% 3.36/3.57      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf('45', plain,
% 3.36/3.57      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['43', '44'])).
% 3.36/3.57  thf('46', plain,
% 3.36/3.57      ((~ (v3_ordinal1 @ sk_A))
% 3.36/3.57         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 3.36/3.57             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['9', '45'])).
% 3.36/3.57  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('48', plain,
% 3.36/3.57      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 3.36/3.57       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('demod', [status(thm)], ['46', '47'])).
% 3.36/3.57  thf('49', plain,
% 3.36/3.57      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 3.36/3.57       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['10'])).
% 3.36/3.57  thf('50', plain,
% 3.36/3.57      (![X41 : $i]:
% 3.36/3.57         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 3.36/3.57  thf(t69_enumset1, axiom,
% 3.36/3.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.36/3.57  thf('51', plain,
% 3.36/3.57      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 3.36/3.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.36/3.57  thf(t70_enumset1, axiom,
% 3.36/3.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.36/3.57  thf('52', plain,
% 3.36/3.57      (![X12 : $i, X13 : $i]:
% 3.36/3.57         ((k1_enumset1 @ X12 @ X12 @ X13) = (k2_tarski @ X12 @ X13))),
% 3.36/3.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.36/3.57  thf(t71_enumset1, axiom,
% 3.36/3.57    (![A:$i,B:$i,C:$i]:
% 3.36/3.57     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 3.36/3.57  thf('53', plain,
% 3.36/3.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.36/3.57         ((k2_enumset1 @ X14 @ X14 @ X15 @ X16)
% 3.36/3.57           = (k1_enumset1 @ X14 @ X15 @ X16))),
% 3.36/3.57      inference('cnf', [status(esa)], [t71_enumset1])).
% 3.36/3.57  thf(t72_enumset1, axiom,
% 3.36/3.57    (![A:$i,B:$i,C:$i,D:$i]:
% 3.36/3.57     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 3.36/3.57  thf('54', plain,
% 3.36/3.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 3.36/3.57         ((k3_enumset1 @ X17 @ X17 @ X18 @ X19 @ X20)
% 3.36/3.57           = (k2_enumset1 @ X17 @ X18 @ X19 @ X20))),
% 3.36/3.57      inference('cnf', [status(esa)], [t72_enumset1])).
% 3.36/3.57  thf(d3_enumset1, axiom,
% 3.36/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.36/3.57     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 3.36/3.57       ( ![G:$i]:
% 3.36/3.57         ( ( r2_hidden @ G @ F ) <=>
% 3.36/3.57           ( ~( ( ( G ) != ( E ) ) & ( ( G ) != ( D ) ) & ( ( G ) != ( C ) ) & 
% 3.36/3.57                ( ( G ) != ( B ) ) & ( ( G ) != ( A ) ) ) ) ) ) ))).
% 3.36/3.57  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $i > $o).
% 3.36/3.57  thf(zf_stmt_2, axiom,
% 3.36/3.57    (![G:$i,E:$i,D:$i,C:$i,B:$i,A:$i]:
% 3.36/3.57     ( ( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) <=>
% 3.36/3.57       ( ( ( G ) != ( A ) ) & ( ( G ) != ( B ) ) & ( ( G ) != ( C ) ) & 
% 3.36/3.57         ( ( G ) != ( D ) ) & ( ( G ) != ( E ) ) ) ))).
% 3.36/3.57  thf(zf_stmt_3, axiom,
% 3.36/3.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.36/3.57     ( ( ( F ) = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) <=>
% 3.36/3.57       ( ![G:$i]:
% 3.36/3.57         ( ( r2_hidden @ G @ F ) <=>
% 3.36/3.57           ( ~( zip_tseitin_0 @ G @ E @ D @ C @ B @ A ) ) ) ) ))).
% 3.36/3.57  thf('55', plain,
% 3.36/3.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.36/3.57         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36)
% 3.36/3.57          | (r2_hidden @ X31 @ X37)
% 3.36/3.57          | ((X37) != (k3_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32)))),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.36/3.57  thf('56', plain,
% 3.36/3.57      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.36/3.57         ((r2_hidden @ X31 @ (k3_enumset1 @ X36 @ X35 @ X34 @ X33 @ X32))
% 3.36/3.57          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 @ X35 @ X36))),
% 3.36/3.57      inference('simplify', [status(thm)], ['55'])).
% 3.36/3.57  thf('57', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.36/3.57         ((r2_hidden @ X4 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0))
% 3.36/3.57          | (zip_tseitin_0 @ X4 @ X0 @ X1 @ X2 @ X3 @ X3))),
% 3.36/3.57      inference('sup+', [status(thm)], ['54', '56'])).
% 3.36/3.57  thf('58', plain,
% 3.36/3.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.36/3.57         (((X25) != (X24))
% 3.36/3.57          | ~ (zip_tseitin_0 @ X25 @ X26 @ X27 @ X28 @ X29 @ X24))),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.36/3.57  thf('59', plain,
% 3.36/3.57      (![X24 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 3.36/3.57         ~ (zip_tseitin_0 @ X24 @ X26 @ X27 @ X28 @ X29 @ X24)),
% 3.36/3.57      inference('simplify', [status(thm)], ['58'])).
% 3.36/3.57  thf('60', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.36/3.57         (r2_hidden @ X0 @ (k2_enumset1 @ X0 @ X1 @ X2 @ X3))),
% 3.36/3.57      inference('sup-', [status(thm)], ['57', '59'])).
% 3.36/3.57  thf('61', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.57         (r2_hidden @ X2 @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 3.36/3.57      inference('sup+', [status(thm)], ['53', '60'])).
% 3.36/3.57  thf('62', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 3.36/3.57      inference('sup+', [status(thm)], ['52', '61'])).
% 3.36/3.57  thf('63', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 3.36/3.57      inference('sup+', [status(thm)], ['51', '62'])).
% 3.36/3.57  thf('64', plain,
% 3.36/3.57      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.36/3.57         (~ (r2_hidden @ X2 @ X3)
% 3.36/3.57          | (r2_hidden @ X2 @ X4)
% 3.36/3.57          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.36/3.57  thf('65', plain,
% 3.36/3.57      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.36/3.57         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 3.36/3.57      inference('simplify', [status(thm)], ['64'])).
% 3.36/3.57  thf('66', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['63', '65'])).
% 3.36/3.57  thf('67', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 3.36/3.57      inference('sup+', [status(thm)], ['50', '66'])).
% 3.36/3.57  thf('68', plain,
% 3.36/3.57      (![X11 : $i]: ((k2_tarski @ X11 @ X11) = (k1_tarski @ X11))),
% 3.36/3.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.36/3.57  thf('69', plain,
% 3.36/3.57      (![X41 : $i]:
% 3.36/3.57         ((k1_ordinal1 @ X41) = (k2_xboole_0 @ X41 @ (k1_tarski @ X41)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d1_ordinal1])).
% 3.36/3.57  thf('70', plain,
% 3.36/3.57      (![X0 : $i]:
% 3.36/3.57         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 3.36/3.57      inference('sup+', [status(thm)], ['68', '69'])).
% 3.36/3.57  thf('71', plain,
% 3.36/3.57      (![X46 : $i, X47 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X46)
% 3.36/3.57          | (r1_ordinal1 @ X47 @ X46)
% 3.36/3.57          | (r2_hidden @ X46 @ X47)
% 3.36/3.57          | ~ (v3_ordinal1 @ X47))),
% 3.36/3.57      inference('cnf', [status(esa)], [t26_ordinal1])).
% 3.36/3.57  thf('72', plain,
% 3.36/3.57      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.36/3.57         (~ (r2_hidden @ X2 @ X5)
% 3.36/3.57          | (r2_hidden @ X2 @ X4)
% 3.36/3.57          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.36/3.57      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.36/3.57  thf('73', plain,
% 3.36/3.57      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.36/3.57         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 3.36/3.57      inference('simplify', [status(thm)], ['72'])).
% 3.36/3.57  thf('74', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X0)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['71', '73'])).
% 3.36/3.57  thf('75', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]:
% 3.36/3.57         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 3.36/3.57          | ~ (v3_ordinal1 @ X1)
% 3.36/3.57          | (r1_ordinal1 @ X0 @ X1)
% 3.36/3.57          | ~ (v3_ordinal1 @ X0))),
% 3.36/3.57      inference('sup+', [status(thm)], ['70', '74'])).
% 3.36/3.57  thf('76', plain,
% 3.36/3.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf('77', plain,
% 3.36/3.57      (((~ (v3_ordinal1 @ sk_B)
% 3.36/3.57         | (r1_ordinal1 @ sk_B @ sk_A)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['75', '76'])).
% 3.36/3.57  thf('78', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('79', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('80', plain,
% 3.36/3.57      (((r1_ordinal1 @ sk_B @ sk_A))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 3.36/3.57  thf(redefinition_r1_ordinal1, axiom,
% 3.36/3.57    (![A:$i,B:$i]:
% 3.36/3.57     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 3.36/3.57       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 3.36/3.57  thf('81', plain,
% 3.36/3.57      (![X42 : $i, X43 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X42)
% 3.36/3.57          | ~ (v3_ordinal1 @ X43)
% 3.36/3.57          | (r1_tarski @ X42 @ X43)
% 3.36/3.57          | ~ (r1_ordinal1 @ X42 @ X43))),
% 3.36/3.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 3.36/3.57  thf('82', plain,
% 3.36/3.57      ((((r1_tarski @ sk_B @ sk_A)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['80', '81'])).
% 3.36/3.57  thf('83', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('84', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('85', plain,
% 3.36/3.57      (((r1_tarski @ sk_B @ sk_A))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['82', '83', '84'])).
% 3.36/3.57  thf('86', plain,
% 3.36/3.57      (![X8 : $i, X10 : $i]:
% 3.36/3.57         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.36/3.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 3.36/3.57  thf('87', plain,
% 3.36/3.57      (((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_B @ sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['85', '86'])).
% 3.36/3.57  thf('88', plain,
% 3.36/3.57      (![X44 : $i, X45 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X44)
% 3.36/3.57          | (r2_hidden @ X45 @ X44)
% 3.36/3.57          | ~ (r2_xboole_0 @ X45 @ X44)
% 3.36/3.57          | ~ (v1_ordinal1 @ X45))),
% 3.36/3.57      inference('cnf', [status(esa)], [t21_ordinal1])).
% 3.36/3.57  thf('89', plain,
% 3.36/3.57      (((((sk_B) = (sk_A))
% 3.36/3.57         | ~ (v1_ordinal1 @ sk_B)
% 3.36/3.57         | (r2_hidden @ sk_B @ sk_A)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('sup-', [status(thm)], ['87', '88'])).
% 3.36/3.57  thf('90', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('91', plain,
% 3.36/3.57      (![X40 : $i]: ((v1_ordinal1 @ X40) | ~ (v3_ordinal1 @ X40))),
% 3.36/3.57      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 3.36/3.57  thf('92', plain, ((v1_ordinal1 @ sk_B)),
% 3.36/3.57      inference('sup-', [status(thm)], ['90', '91'])).
% 3.36/3.57  thf('93', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('94', plain,
% 3.36/3.57      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('demod', [status(thm)], ['89', '92', '93'])).
% 3.36/3.57  thf('95', plain,
% 3.36/3.57      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('split', [status(esa)], ['10'])).
% 3.36/3.57  thf('96', plain,
% 3.36/3.57      (![X42 : $i, X43 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X42)
% 3.36/3.57          | ~ (v3_ordinal1 @ X43)
% 3.36/3.57          | (r1_tarski @ X42 @ X43)
% 3.36/3.57          | ~ (r1_ordinal1 @ X42 @ X43))),
% 3.36/3.57      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 3.36/3.57  thf('97', plain,
% 3.36/3.57      ((((r1_tarski @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['95', '96'])).
% 3.36/3.57  thf('98', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('99', plain, ((v3_ordinal1 @ sk_A)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('100', plain,
% 3.36/3.57      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('demod', [status(thm)], ['97', '98', '99'])).
% 3.36/3.57  thf('101', plain,
% 3.36/3.57      (![X8 : $i, X10 : $i]:
% 3.36/3.57         ((r2_xboole_0 @ X8 @ X10) | ((X8) = (X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.36/3.57      inference('cnf', [status(esa)], [d8_xboole_0])).
% 3.36/3.57  thf('102', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B)))
% 3.36/3.57         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['100', '101'])).
% 3.36/3.57  thf('103', plain,
% 3.36/3.57      (![X44 : $i, X45 : $i]:
% 3.36/3.57         (~ (v3_ordinal1 @ X44)
% 3.36/3.57          | (r2_hidden @ X45 @ X44)
% 3.36/3.57          | ~ (r2_xboole_0 @ X45 @ X44)
% 3.36/3.57          | ~ (v1_ordinal1 @ X45))),
% 3.36/3.57      inference('cnf', [status(esa)], [t21_ordinal1])).
% 3.36/3.57  thf('104', plain,
% 3.36/3.57      (((((sk_A) = (sk_B))
% 3.36/3.57         | ~ (v1_ordinal1 @ sk_A)
% 3.36/3.57         | (r2_hidden @ sk_A @ sk_B)
% 3.36/3.57         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['102', '103'])).
% 3.36/3.57  thf('105', plain, ((v1_ordinal1 @ sk_A)),
% 3.36/3.57      inference('sup-', [status(thm)], ['32', '33'])).
% 3.36/3.57  thf('106', plain, ((v3_ordinal1 @ sk_B)),
% 3.36/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.36/3.57  thf('107', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 3.36/3.57         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('demod', [status(thm)], ['104', '105', '106'])).
% 3.36/3.57  thf('108', plain,
% 3.36/3.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 3.36/3.57      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 3.36/3.57  thf('109', plain,
% 3.36/3.57      (((((sk_A) = (sk_B)) | ~ (r2_hidden @ sk_B @ sk_A)))
% 3.36/3.57         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['107', '108'])).
% 3.36/3.57  thf('110', plain,
% 3.36/3.57      (((((sk_B) = (sk_A)) | ((sk_A) = (sk_B))))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 3.36/3.57             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['94', '109'])).
% 3.36/3.57  thf('111', plain,
% 3.36/3.57      ((((sk_B) = (sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 3.36/3.57             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('simplify', [status(thm)], ['110'])).
% 3.36/3.57  thf('112', plain,
% 3.36/3.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 3.36/3.57      inference('split', [status(esa)], ['0'])).
% 3.36/3.57  thf('113', plain,
% 3.36/3.57      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 3.36/3.57         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 3.36/3.57             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['111', '112'])).
% 3.36/3.57  thf('114', plain,
% 3.36/3.57      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 3.36/3.57       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 3.36/3.57      inference('sup-', [status(thm)], ['67', '113'])).
% 3.36/3.57  thf('115', plain, ($false),
% 3.36/3.57      inference('sat_resolution*', [status(thm)], ['1', '48', '49', '114'])).
% 3.36/3.57  
% 3.36/3.57  % SZS output end Refutation
% 3.36/3.57  
% 3.36/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
