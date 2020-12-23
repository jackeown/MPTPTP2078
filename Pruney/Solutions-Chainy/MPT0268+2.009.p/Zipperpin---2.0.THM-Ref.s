%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBjrb69uBI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:53 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 162 expanded)
%              Number of leaves         :   30 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  777 (1212 expanded)
%              Number of equality atoms :   78 ( 126 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X27 @ X31 )
      | ( X31
       != ( k1_enumset1 @ X30 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ ( k1_enumset1 @ X30 @ X29 @ X28 ) )
      | ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X22 )
      | ~ ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ~ ( zip_tseitin_0 @ X22 @ X24 @ X25 @ X22 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X44 ) @ X45 )
      | ( r2_hidden @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['44','47','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('74',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBjrb69uBI
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.94  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.94  % Solved by: fo/fo7.sh
% 0.75/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.94  % done 1008 iterations in 0.482s
% 0.75/0.94  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.94  % SZS output start Refutation
% 0.75/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.94  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.75/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.94  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.75/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.94  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.94  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.94  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.75/0.94  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.94  thf(t65_zfmisc_1, conjecture,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.94       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.75/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.94    (~( ![A:$i,B:$i]:
% 0.75/0.94        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.94          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.75/0.94    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.75/0.94  thf('0', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ sk_A)
% 0.75/0.94        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('1', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.94       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('2', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf(t70_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.75/0.94  thf('3', plain,
% 0.75/0.94      (![X35 : $i, X36 : $i]:
% 0.75/0.94         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.75/0.94      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.75/0.94  thf(d1_enumset1, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=>
% 0.75/0.94           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.75/0.94  thf(zf_stmt_2, axiom,
% 0.75/0.94    (![E:$i,C:$i,B:$i,A:$i]:
% 0.75/0.94     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.75/0.94       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.75/0.94  thf(zf_stmt_3, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.94     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.75/0.94       ( ![E:$i]:
% 0.75/0.94         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.75/0.94  thf('4', plain,
% 0.75/0.94      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.94         ((zip_tseitin_0 @ X27 @ X28 @ X29 @ X30)
% 0.75/0.94          | (r2_hidden @ X27 @ X31)
% 0.75/0.94          | ((X31) != (k1_enumset1 @ X30 @ X29 @ X28)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.75/0.94  thf('5', plain,
% 0.75/0.94      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.75/0.94         ((r2_hidden @ X27 @ (k1_enumset1 @ X30 @ X29 @ X28))
% 0.75/0.94          | (zip_tseitin_0 @ X27 @ X28 @ X29 @ X30))),
% 0.75/0.94      inference('simplify', [status(thm)], ['4'])).
% 0.75/0.94  thf('6', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.75/0.94          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['3', '5'])).
% 0.75/0.94  thf('7', plain,
% 0.75/0.94      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.75/0.94         (((X23) != (X22)) | ~ (zip_tseitin_0 @ X23 @ X24 @ X25 @ X22))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.94  thf('8', plain,
% 0.75/0.94      (![X22 : $i, X24 : $i, X25 : $i]:
% 0.75/0.94         ~ (zip_tseitin_0 @ X22 @ X24 @ X25 @ X22)),
% 0.75/0.94      inference('simplify', [status(thm)], ['7'])).
% 0.75/0.94  thf('9', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['6', '8'])).
% 0.75/0.94  thf(t69_enumset1, axiom,
% 0.75/0.94    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.75/0.94  thf('10', plain,
% 0.75/0.94      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.75/0.94      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.75/0.94  thf(d10_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.94  thf('11', plain,
% 0.75/0.94      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.75/0.94  thf('12', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.75/0.94      inference('simplify', [status(thm)], ['11'])).
% 0.75/0.94  thf(t28_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.94  thf('13', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i]:
% 0.75/0.94         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.75/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.94  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf(l27_zfmisc_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.75/0.94  thf('15', plain,
% 0.75/0.94      (![X44 : $i, X45 : $i]:
% 0.75/0.94         ((r1_xboole_0 @ (k1_tarski @ X44) @ X45) | (r2_hidden @ X44 @ X45))),
% 0.75/0.94      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.75/0.94  thf(t83_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.94  thf('16', plain,
% 0.75/0.94      (![X19 : $i, X20 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.75/0.94      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.94  thf('17', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((r2_hidden @ X1 @ X0)
% 0.75/0.94          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.94  thf(t48_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.75/0.94  thf('18', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.75/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('19', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.75/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('20', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.94           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['18', '19'])).
% 0.75/0.94  thf(d5_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i,C:$i]:
% 0.75/0.94     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.75/0.94       ( ![D:$i]:
% 0.75/0.94         ( ( r2_hidden @ D @ C ) <=>
% 0.75/0.94           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.75/0.94  thf('21', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.94          | ~ (r2_hidden @ X6 @ X4)
% 0.75/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.94  thf('22', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.94          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['21'])).
% 0.75/0.94  thf('23', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.75/0.94          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['20', '22'])).
% 0.75/0.94  thf('24', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ 
% 0.75/0.94             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 0.75/0.94          | (r2_hidden @ X0 @ X1)
% 0.75/0.94          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['17', '23'])).
% 0.75/0.94  thf('25', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf('26', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.75/0.94          | (r2_hidden @ X0 @ X1)
% 0.75/0.94          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.75/0.94      inference('demod', [status(thm)], ['24', '25'])).
% 0.75/0.94  thf('27', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.75/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('28', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X5)
% 0.75/0.94          | (r2_hidden @ X6 @ X3)
% 0.75/0.94          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.75/0.94  thf('29', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.94         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['28'])).
% 0.75/0.94  thf('30', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.75/0.94      inference('sup-', [status(thm)], ['27', '29'])).
% 0.75/0.94  thf('31', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.94          | (r2_hidden @ X0 @ X1))),
% 0.75/0.94      inference('clc', [status(thm)], ['26', '30'])).
% 0.75/0.94  thf('32', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.75/0.94          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['14', '31'])).
% 0.75/0.94  thf('33', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.75/0.94          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['10', '32'])).
% 0.75/0.94  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['9', '33'])).
% 0.75/0.94  thf('35', plain,
% 0.75/0.94      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.75/0.94        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.94  thf('36', plain,
% 0.75/0.94      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.75/0.94         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('split', [status(esa)], ['35'])).
% 0.75/0.94  thf('37', plain,
% 0.75/0.94      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.75/0.94         (~ (r2_hidden @ X6 @ X4)
% 0.75/0.94          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.75/0.94      inference('simplify', [status(thm)], ['21'])).
% 0.75/0.94  thf('38', plain,
% 0.75/0.94      ((![X0 : $i]:
% 0.75/0.94          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.75/0.94         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.94  thf('39', plain,
% 0.75/0.94      ((~ (r2_hidden @ sk_B @ sk_A))
% 0.75/0.94         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['34', '38'])).
% 0.75/0.94  thf('40', plain,
% 0.75/0.94      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.94       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['2', '39'])).
% 0.75/0.94  thf('41', plain,
% 0.75/0.94      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.94       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.94      inference('split', [status(esa)], ['35'])).
% 0.75/0.94  thf('42', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((r2_hidden @ X1 @ X0)
% 0.75/0.94          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/0.94  thf('43', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.75/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('44', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.75/0.94            = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.94          | (r2_hidden @ X0 @ X1))),
% 0.75/0.94      inference('sup+', [status(thm)], ['42', '43'])).
% 0.75/0.94  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.94  thf(t100_xboole_1, axiom,
% 0.75/0.94    (![A:$i,B:$i]:
% 0.75/0.94     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.94  thf('46', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('47', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf(t3_boole, axiom,
% 0.75/0.94    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.94  thf('48', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('49', plain,
% 0.75/0.94      (![X17 : $i, X18 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.75/0.94           = (k3_xboole_0 @ X17 @ X18))),
% 0.75/0.94      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.75/0.94  thf('50', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['48', '49'])).
% 0.75/0.94  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.94  thf('51', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.75/0.94      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.94  thf('52', plain,
% 0.75/0.94      (![X13 : $i, X14 : $i]:
% 0.75/0.94         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.75/0.94      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.94  thf('53', plain,
% 0.75/0.94      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.94  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.94    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.94  thf('54', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('55', plain,
% 0.75/0.94      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.94  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['50', '55'])).
% 0.75/0.94  thf('57', plain,
% 0.75/0.94      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['45', '46'])).
% 0.75/0.94  thf('58', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.75/0.94      inference('demod', [status(thm)], ['56', '57'])).
% 0.75/0.94  thf('59', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k1_xboole_0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.75/0.94          | (r2_hidden @ X0 @ X1))),
% 0.75/0.94      inference('demod', [status(thm)], ['44', '47', '58'])).
% 0.75/0.94  thf('60', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.94      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.94  thf('61', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('62', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ X1)
% 0.75/0.94           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.94      inference('sup+', [status(thm)], ['60', '61'])).
% 0.75/0.94  thf('63', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.75/0.94            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.75/0.94          | (r2_hidden @ X1 @ X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['59', '62'])).
% 0.75/0.94  thf('64', plain,
% 0.75/0.94      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.94  thf('65', plain,
% 0.75/0.94      (![X11 : $i, X12 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X11 @ X12)
% 0.75/0.94           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.75/0.94      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.94  thf('66', plain,
% 0.75/0.94      (![X0 : $i]:
% 0.75/0.94         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['64', '65'])).
% 0.75/0.94  thf('67', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.75/0.94      inference('cnf', [status(esa)], [t3_boole])).
% 0.75/0.94  thf('68', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.94      inference('sup+', [status(thm)], ['66', '67'])).
% 0.75/0.94  thf('69', plain,
% 0.75/0.94      (![X0 : $i, X1 : $i]:
% 0.75/0.94         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.75/0.94          | (r2_hidden @ X1 @ X0))),
% 0.75/0.94      inference('demod', [status(thm)], ['63', '68'])).
% 0.75/0.94  thf('70', plain,
% 0.75/0.94      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.75/0.94         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('split', [status(esa)], ['0'])).
% 0.75/0.94  thf('71', plain,
% 0.75/0.94      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.75/0.94         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.94  thf('72', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ sk_A))
% 0.75/0.94         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.75/0.94      inference('simplify', [status(thm)], ['71'])).
% 0.75/0.94  thf('73', plain,
% 0.75/0.94      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.75/0.94      inference('split', [status(esa)], ['35'])).
% 0.75/0.94  thf('74', plain,
% 0.75/0.94      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.75/0.94       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.75/0.94      inference('sup-', [status(thm)], ['72', '73'])).
% 0.75/0.94  thf('75', plain, ($false),
% 0.75/0.94      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '74'])).
% 0.75/0.94  
% 0.75/0.94  % SZS output end Refutation
% 0.75/0.94  
% 0.75/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
