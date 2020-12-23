%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G9lEq4PEcC

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 265 expanded)
%              Number of leaves         :   31 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  847 (2076 expanded)
%              Number of equality atoms :   86 ( 208 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_enumset1 @ X40 @ X40 @ X41 )
      = ( k2_tarski @ X40 @ X41 ) ) ),
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

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X32 @ X36 )
      | ( X36
       != ( k1_enumset1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('7',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X32 @ ( k1_enumset1 @ X35 @ X34 @ X33 ) )
      | ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X28 != X27 )
      | ~ ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X29 @ X30 @ X27 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('17',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X45 ) @ X46 )
      | ( r2_hidden @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k4_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','40'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('66',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','77'])).

thf('79',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','41','80'])).

thf('82',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','82'])).

thf('84',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['43','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G9lEq4PEcC
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.22  % Solved by: fo/fo7.sh
% 1.02/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.22  % done 1625 iterations in 0.775s
% 1.02/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.22  % SZS output start Refutation
% 1.02/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.22  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.02/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.02/1.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.02/1.22  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.22  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.02/1.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.22  thf(t65_zfmisc_1, conjecture,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.02/1.22       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.02/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.22    (~( ![A:$i,B:$i]:
% 1.02/1.22        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.02/1.22          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.02/1.22    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.02/1.22  thf('0', plain,
% 1.02/1.22      ((~ (r2_hidden @ sk_B @ sk_A)
% 1.02/1.22        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('1', plain,
% 1.02/1.22      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 1.02/1.22      inference('split', [status(esa)], ['0'])).
% 1.02/1.22  thf('2', plain,
% 1.02/1.22      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 1.02/1.22       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.22      inference('split', [status(esa)], ['0'])).
% 1.02/1.22  thf('3', plain,
% 1.02/1.22      (((r2_hidden @ sk_B @ sk_A)
% 1.02/1.22        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('4', plain,
% 1.02/1.22      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 1.02/1.22      inference('split', [status(esa)], ['3'])).
% 1.02/1.22  thf(t70_enumset1, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.02/1.22  thf('5', plain,
% 1.02/1.22      (![X40 : $i, X41 : $i]:
% 1.02/1.22         ((k1_enumset1 @ X40 @ X40 @ X41) = (k2_tarski @ X40 @ X41))),
% 1.02/1.22      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.02/1.22  thf(d1_enumset1, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.22     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.22       ( ![E:$i]:
% 1.02/1.22         ( ( r2_hidden @ E @ D ) <=>
% 1.02/1.22           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.02/1.22  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.02/1.22  thf(zf_stmt_2, axiom,
% 1.02/1.22    (![E:$i,C:$i,B:$i,A:$i]:
% 1.02/1.22     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.02/1.22       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.02/1.22  thf(zf_stmt_3, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.22     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.02/1.22       ( ![E:$i]:
% 1.02/1.22         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.02/1.22  thf('6', plain,
% 1.02/1.22      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.02/1.23         ((zip_tseitin_0 @ X32 @ X33 @ X34 @ X35)
% 1.02/1.23          | (r2_hidden @ X32 @ X36)
% 1.02/1.23          | ((X36) != (k1_enumset1 @ X35 @ X34 @ X33)))),
% 1.02/1.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.23  thf('7', plain,
% 1.02/1.23      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.02/1.23         ((r2_hidden @ X32 @ (k1_enumset1 @ X35 @ X34 @ X33))
% 1.02/1.23          | (zip_tseitin_0 @ X32 @ X33 @ X34 @ X35))),
% 1.02/1.23      inference('simplify', [status(thm)], ['6'])).
% 1.02/1.23  thf('8', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.02/1.23          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['5', '7'])).
% 1.02/1.23  thf('9', plain,
% 1.02/1.23      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.02/1.23         (((X28) != (X27)) | ~ (zip_tseitin_0 @ X28 @ X29 @ X30 @ X27))),
% 1.02/1.23      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.23  thf('10', plain,
% 1.02/1.23      (![X27 : $i, X29 : $i, X30 : $i]:
% 1.02/1.23         ~ (zip_tseitin_0 @ X27 @ X29 @ X30 @ X27)),
% 1.02/1.23      inference('simplify', [status(thm)], ['9'])).
% 1.02/1.23  thf('11', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.02/1.23      inference('sup-', [status(thm)], ['8', '10'])).
% 1.02/1.23  thf(t69_enumset1, axiom,
% 1.02/1.23    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.02/1.23  thf('12', plain,
% 1.02/1.23      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 1.02/1.23      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.02/1.23  thf(d10_xboole_0, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.02/1.23  thf('13', plain,
% 1.02/1.23      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 1.02/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.02/1.23  thf('14', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.02/1.23      inference('simplify', [status(thm)], ['13'])).
% 1.02/1.23  thf(t28_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.02/1.23  thf('15', plain,
% 1.02/1.23      (![X16 : $i, X17 : $i]:
% 1.02/1.23         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 1.02/1.23      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.02/1.23  thf('16', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.02/1.23  thf(l27_zfmisc_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.02/1.23  thf('17', plain,
% 1.02/1.23      (![X45 : $i, X46 : $i]:
% 1.02/1.23         ((r1_xboole_0 @ (k1_tarski @ X45) @ X46) | (r2_hidden @ X45 @ X46))),
% 1.02/1.23      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.02/1.23  thf(t83_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.02/1.23  thf('18', plain,
% 1.02/1.23      (![X24 : $i, X25 : $i]:
% 1.02/1.23         (((k4_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_xboole_0 @ X24 @ X25))),
% 1.02/1.23      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.02/1.23  thf('19', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((r2_hidden @ X1 @ X0)
% 1.02/1.23          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['17', '18'])).
% 1.02/1.23  thf(t48_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.02/1.23  thf('20', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.02/1.23           = (k3_xboole_0 @ X19 @ X20))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('21', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.02/1.23           = (k3_xboole_0 @ X19 @ X20))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('22', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['20', '21'])).
% 1.02/1.23  thf(d5_xboole_0, axiom,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.02/1.23       ( ![D:$i]:
% 1.02/1.23         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.23           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.02/1.23  thf('23', plain,
% 1.02/1.23      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X6 @ X5)
% 1.02/1.23          | ~ (r2_hidden @ X6 @ X4)
% 1.02/1.23          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.02/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.02/1.23  thf('24', plain,
% 1.02/1.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X6 @ X4)
% 1.02/1.23          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.02/1.23      inference('simplify', [status(thm)], ['23'])).
% 1.02/1.23  thf('25', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 1.02/1.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['22', '24'])).
% 1.02/1.23  thf('26', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X2 @ 
% 1.02/1.23             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 1.02/1.23          | (r2_hidden @ X0 @ X1)
% 1.02/1.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['19', '25'])).
% 1.02/1.23  thf('27', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.02/1.23  thf('28', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 1.02/1.23          | (r2_hidden @ X0 @ X1)
% 1.02/1.23          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 1.02/1.23      inference('demod', [status(thm)], ['26', '27'])).
% 1.02/1.23  thf('29', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.02/1.23           = (k3_xboole_0 @ X19 @ X20))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('30', plain,
% 1.02/1.23      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X6 @ X5)
% 1.02/1.23          | (r2_hidden @ X6 @ X3)
% 1.02/1.23          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 1.02/1.23      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.02/1.23  thf('31', plain,
% 1.02/1.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.23         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.02/1.23      inference('simplify', [status(thm)], ['30'])).
% 1.02/1.23  thf('32', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.02/1.23      inference('sup-', [status(thm)], ['29', '31'])).
% 1.02/1.23  thf('33', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 1.02/1.23          | (r2_hidden @ X0 @ X1))),
% 1.02/1.23      inference('clc', [status(thm)], ['28', '32'])).
% 1.02/1.23  thf('34', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 1.02/1.23          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['16', '33'])).
% 1.02/1.23  thf('35', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 1.02/1.23          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['12', '34'])).
% 1.02/1.23  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['11', '35'])).
% 1.02/1.23  thf('37', plain,
% 1.02/1.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 1.02/1.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.23      inference('split', [status(esa)], ['0'])).
% 1.02/1.23  thf('38', plain,
% 1.02/1.23      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.02/1.23         (~ (r2_hidden @ X6 @ X4)
% 1.02/1.23          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 1.02/1.23      inference('simplify', [status(thm)], ['23'])).
% 1.02/1.23  thf('39', plain,
% 1.02/1.23      ((![X0 : $i]:
% 1.02/1.23          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 1.02/1.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.23      inference('sup-', [status(thm)], ['37', '38'])).
% 1.02/1.23  thf('40', plain,
% 1.02/1.23      ((~ (r2_hidden @ sk_B @ sk_A))
% 1.02/1.23         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.23      inference('sup-', [status(thm)], ['36', '39'])).
% 1.02/1.23  thf('41', plain,
% 1.02/1.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.02/1.23       ~ ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.23      inference('sup-', [status(thm)], ['4', '40'])).
% 1.02/1.23  thf('42', plain, (~ ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.23      inference('sat_resolution*', [status(thm)], ['2', '41'])).
% 1.02/1.23  thf('43', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 1.02/1.23      inference('simpl_trail', [status(thm)], ['1', '42'])).
% 1.02/1.23  thf('44', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((r2_hidden @ X1 @ X0)
% 1.02/1.23          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 1.02/1.23      inference('sup-', [status(thm)], ['17', '18'])).
% 1.02/1.23  thf('45', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.02/1.23           = (k3_xboole_0 @ X19 @ X20))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('46', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.02/1.23  thf(t49_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i,C:$i]:
% 1.02/1.23     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.02/1.23       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.02/1.23  thf('47', plain,
% 1.02/1.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 1.02/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23))),
% 1.02/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.02/1.23  thf('48', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.02/1.23           = (k4_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['46', '47'])).
% 1.02/1.23  thf(commutativity_k3_xboole_0, axiom,
% 1.02/1.23    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.02/1.23  thf('49', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.02/1.23      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.02/1.23  thf(t100_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.02/1.23  thf('50', plain,
% 1.02/1.23      (![X14 : $i, X15 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X14 @ X15)
% 1.02/1.23           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.23  thf('51', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ X1)
% 1.02/1.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['49', '50'])).
% 1.02/1.23  thf('52', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.02/1.23           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['48', '51'])).
% 1.02/1.23  thf('53', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['14', '15'])).
% 1.02/1.23  thf('54', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ X1)
% 1.02/1.23           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.23      inference('sup+', [status(thm)], ['49', '50'])).
% 1.02/1.23  thf('55', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['53', '54'])).
% 1.02/1.23  thf('56', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 1.02/1.23      inference('simplify', [status(thm)], ['13'])).
% 1.02/1.23  thf(l32_xboole_1, axiom,
% 1.02/1.23    (![A:$i,B:$i]:
% 1.02/1.23     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.23  thf('57', plain,
% 1.02/1.23      (![X11 : $i, X13 : $i]:
% 1.02/1.23         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 1.02/1.23          | ~ (r1_tarski @ X11 @ X13))),
% 1.02/1.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.02/1.23  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.23  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['55', '58'])).
% 1.02/1.23  thf('60', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['52', '59'])).
% 1.02/1.23  thf('61', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['45', '60'])).
% 1.02/1.23  thf('62', plain,
% 1.02/1.23      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 1.02/1.23           = (k4_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23))),
% 1.02/1.23      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.02/1.23  thf('63', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['61', '62'])).
% 1.02/1.23  thf('64', plain,
% 1.02/1.23      (![X14 : $i, X15 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X14 @ X15)
% 1.02/1.23           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.23  thf('65', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.02/1.23           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['63', '64'])).
% 1.02/1.23  thf(t3_boole, axiom,
% 1.02/1.23    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.02/1.23  thf('66', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('67', plain,
% 1.02/1.23      (![X19 : $i, X20 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 1.02/1.23           = (k3_xboole_0 @ X19 @ X20))),
% 1.02/1.23      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.02/1.23  thf('68', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['66', '67'])).
% 1.02/1.23  thf('69', plain,
% 1.02/1.23      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['53', '54'])).
% 1.02/1.23  thf('70', plain,
% 1.02/1.23      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('demod', [status(thm)], ['68', '69'])).
% 1.02/1.23  thf('71', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['55', '58'])).
% 1.02/1.23  thf('72', plain,
% 1.02/1.23      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['70', '71'])).
% 1.02/1.23  thf('73', plain,
% 1.02/1.23      (![X14 : $i, X15 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X14 @ X15)
% 1.02/1.23           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.02/1.23      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.02/1.23  thf('74', plain,
% 1.02/1.23      (![X0 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['72', '73'])).
% 1.02/1.23  thf('75', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 1.02/1.23      inference('cnf', [status(esa)], [t3_boole])).
% 1.02/1.23  thf('76', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.02/1.23      inference('sup+', [status(thm)], ['74', '75'])).
% 1.02/1.23  thf('77', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.02/1.23      inference('demod', [status(thm)], ['65', '76'])).
% 1.02/1.23  thf('78', plain,
% 1.02/1.23      (![X0 : $i, X1 : $i]:
% 1.02/1.23         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.02/1.23          | (r2_hidden @ X0 @ X1))),
% 1.02/1.23      inference('sup+', [status(thm)], ['44', '77'])).
% 1.02/1.23  thf('79', plain,
% 1.02/1.23      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 1.02/1.23         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 1.02/1.23      inference('split', [status(esa)], ['3'])).
% 1.02/1.23  thf('80', plain,
% 1.02/1.23      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) | 
% 1.02/1.23       ((r2_hidden @ sk_B @ sk_A))),
% 1.02/1.23      inference('split', [status(esa)], ['3'])).
% 1.02/1.23  thf('81', plain, (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 1.02/1.23      inference('sat_resolution*', [status(thm)], ['2', '41', '80'])).
% 1.02/1.23  thf('82', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A))),
% 1.02/1.23      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 1.02/1.23  thf('83', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A))),
% 1.02/1.23      inference('sup-', [status(thm)], ['78', '82'])).
% 1.02/1.23  thf('84', plain, ((r2_hidden @ sk_B @ sk_A)),
% 1.02/1.23      inference('simplify', [status(thm)], ['83'])).
% 1.02/1.23  thf('85', plain, ($false), inference('demod', [status(thm)], ['43', '84'])).
% 1.02/1.23  
% 1.02/1.23  % SZS output end Refutation
% 1.02/1.23  
% 1.09/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
