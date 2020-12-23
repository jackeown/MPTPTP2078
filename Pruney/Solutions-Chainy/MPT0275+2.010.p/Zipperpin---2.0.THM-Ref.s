%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G9a3frcM8H

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:37 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 169 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  820 (1578 expanded)
%              Number of equality atoms :   74 ( 148 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
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

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X25 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ( ( k4_xboole_0 @ X15 @ X16 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
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

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('30',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf(t53_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf('35',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ~ ( r2_hidden @ X51 @ X50 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X49 @ X51 ) @ X50 )
        = ( k2_tarski @ X49 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t53_zfmisc_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_C @ sk_C ) )
          = ( k2_tarski @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ X0 ) )
          = ( k2_tarski @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['36','40','41','42'])).

thf('44',plain,
    ( ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('53',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('62',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('63',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','59','60','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G9a3frcM8H
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.66/1.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.84  % Solved by: fo/fo7.sh
% 1.66/1.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.84  % done 1584 iterations in 1.395s
% 1.66/1.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.84  % SZS output start Refutation
% 1.66/1.84  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.66/1.84  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.84  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.66/1.84  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.66/1.84  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.66/1.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.66/1.84  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.66/1.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.66/1.84  thf(t73_zfmisc_1, conjecture,
% 1.66/1.84    (![A:$i,B:$i,C:$i]:
% 1.66/1.84     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 1.66/1.84       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.66/1.84  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.84    (~( ![A:$i,B:$i,C:$i]:
% 1.66/1.84        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 1.66/1.84          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 1.66/1.84    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 1.66/1.84  thf('0', plain,
% 1.66/1.84      (((r2_hidden @ sk_B @ sk_C)
% 1.66/1.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.84  thf('1', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ((r2_hidden @ sk_B @ sk_C))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf(t70_enumset1, axiom,
% 1.66/1.84    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.66/1.84  thf('2', plain,
% 1.66/1.84      (![X35 : $i, X36 : $i]:
% 1.66/1.84         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 1.66/1.84      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.66/1.84  thf(d1_enumset1, axiom,
% 1.66/1.84    (![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.84     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.66/1.84       ( ![E:$i]:
% 1.66/1.84         ( ( r2_hidden @ E @ D ) <=>
% 1.66/1.84           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.66/1.84  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.66/1.84  thf(zf_stmt_2, axiom,
% 1.66/1.84    (![E:$i,C:$i,B:$i,A:$i]:
% 1.66/1.84     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.66/1.84       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.66/1.84  thf(zf_stmt_3, axiom,
% 1.66/1.84    (![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.84     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.66/1.84       ( ![E:$i]:
% 1.66/1.84         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.66/1.84  thf('3', plain,
% 1.66/1.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.66/1.84         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 1.66/1.84          | (r2_hidden @ X28 @ X32)
% 1.66/1.84          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.66/1.84  thf('4', plain,
% 1.66/1.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.66/1.84         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 1.66/1.84          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 1.66/1.84      inference('simplify', [status(thm)], ['3'])).
% 1.66/1.84  thf('5', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.66/1.84          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.66/1.84      inference('sup+', [status(thm)], ['2', '4'])).
% 1.66/1.84  thf('6', plain,
% 1.66/1.84      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.84         (((X24) != (X25)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.66/1.84  thf('7', plain,
% 1.66/1.84      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.66/1.84         ~ (zip_tseitin_0 @ X25 @ X25 @ X26 @ X23)),
% 1.66/1.84      inference('simplify', [status(thm)], ['6'])).
% 1.66/1.84  thf('8', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.66/1.84      inference('sup-', [status(thm)], ['5', '7'])).
% 1.66/1.84  thf('9', plain,
% 1.66/1.84      (((r2_hidden @ sk_A @ sk_C)
% 1.66/1.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.84  thf('10', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('split', [status(esa)], ['9'])).
% 1.66/1.84  thf(l32_xboole_1, axiom,
% 1.66/1.84    (![A:$i,B:$i]:
% 1.66/1.84     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.66/1.84  thf('11', plain,
% 1.66/1.84      (![X15 : $i, X16 : $i]:
% 1.66/1.84         ((r1_tarski @ X15 @ X16)
% 1.66/1.84          | ((k4_xboole_0 @ X15 @ X16) != (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.66/1.84  thf('12', plain,
% 1.66/1.84      (((((k1_xboole_0) != (k1_xboole_0))
% 1.66/1.84         | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['10', '11'])).
% 1.66/1.84  thf('13', plain,
% 1.66/1.84      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('simplify', [status(thm)], ['12'])).
% 1.66/1.84  thf(t28_xboole_1, axiom,
% 1.66/1.84    (![A:$i,B:$i]:
% 1.66/1.84     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.66/1.84  thf('14', plain,
% 1.66/1.84      (![X20 : $i, X21 : $i]:
% 1.66/1.84         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.66/1.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.66/1.84  thf('15', plain,
% 1.66/1.84      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.66/1.84          = (k2_tarski @ sk_A @ sk_B)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['13', '14'])).
% 1.66/1.84  thf(commutativity_k3_xboole_0, axiom,
% 1.66/1.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.66/1.84  thf('16', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.84  thf('17', plain,
% 1.66/1.84      ((((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.66/1.84          = (k2_tarski @ sk_A @ sk_B)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('demod', [status(thm)], ['15', '16'])).
% 1.66/1.84  thf('18', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.84  thf(d4_xboole_0, axiom,
% 1.66/1.84    (![A:$i,B:$i,C:$i]:
% 1.66/1.84     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.66/1.84       ( ![D:$i]:
% 1.66/1.84         ( ( r2_hidden @ D @ C ) <=>
% 1.66/1.84           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.66/1.84  thf('19', plain,
% 1.66/1.84      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X6 @ X5)
% 1.66/1.84          | (r2_hidden @ X6 @ X4)
% 1.66/1.84          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.66/1.84      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.66/1.84  thf('20', plain,
% 1.66/1.84      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.66/1.84         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.66/1.84      inference('simplify', [status(thm)], ['19'])).
% 1.66/1.84  thf('21', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.66/1.84      inference('sup-', [status(thm)], ['18', '20'])).
% 1.66/1.84  thf('22', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.66/1.84           | (r2_hidden @ X0 @ sk_C)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['17', '21'])).
% 1.66/1.84  thf('23', plain,
% 1.66/1.84      (((r2_hidden @ sk_B @ sk_C))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['8', '22'])).
% 1.66/1.84  thf('24', plain,
% 1.66/1.84      ((~ (r2_hidden @ sk_B @ sk_C)
% 1.66/1.84        | ~ (r2_hidden @ sk_A @ sk_C)
% 1.66/1.84        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.84  thf('25', plain,
% 1.66/1.84      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('split', [status(esa)], ['24'])).
% 1.66/1.84  thf('26', plain,
% 1.66/1.84      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ((r2_hidden @ sk_B @ sk_C))),
% 1.66/1.84      inference('sup-', [status(thm)], ['23', '25'])).
% 1.66/1.84  thf('27', plain,
% 1.66/1.84      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 1.66/1.84       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ~ ((r2_hidden @ sk_B @ sk_C))),
% 1.66/1.84      inference('split', [status(esa)], ['24'])).
% 1.66/1.84  thf('28', plain,
% 1.66/1.84      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('split', [status(esa)], ['0'])).
% 1.66/1.84  thf('29', plain,
% 1.66/1.84      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('split', [status(esa)], ['9'])).
% 1.66/1.84  thf('30', plain,
% 1.66/1.84      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('split', [status(esa)], ['9'])).
% 1.66/1.84  thf('31', plain,
% 1.66/1.84      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X2 @ X3)
% 1.66/1.84          | ~ (r2_hidden @ X2 @ X4)
% 1.66/1.84          | (r2_hidden @ X2 @ X5)
% 1.66/1.84          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.66/1.84      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.66/1.84  thf('32', plain,
% 1.66/1.84      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.84         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.66/1.84          | ~ (r2_hidden @ X2 @ X4)
% 1.66/1.84          | ~ (r2_hidden @ X2 @ X3))),
% 1.66/1.84      inference('simplify', [status(thm)], ['31'])).
% 1.66/1.84  thf('33', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (~ (r2_hidden @ sk_A @ X0)
% 1.66/1.84           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['30', '32'])).
% 1.66/1.84  thf('34', plain,
% 1.66/1.84      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_C @ sk_C)))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['29', '33'])).
% 1.66/1.84  thf(t53_zfmisc_1, axiom,
% 1.66/1.84    (![A:$i,B:$i,C:$i]:
% 1.66/1.84     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 1.66/1.84       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 1.66/1.84  thf('35', plain,
% 1.66/1.84      (![X49 : $i, X50 : $i, X51 : $i]:
% 1.66/1.84         (~ (r2_hidden @ X49 @ X50)
% 1.66/1.84          | ~ (r2_hidden @ X51 @ X50)
% 1.66/1.84          | ((k3_xboole_0 @ (k2_tarski @ X49 @ X51) @ X50)
% 1.66/1.84              = (k2_tarski @ X49 @ X51)))),
% 1.66/1.84      inference('cnf', [status(esa)], [t53_zfmisc_1])).
% 1.66/1.84  thf('36', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (((k3_xboole_0 @ (k2_tarski @ sk_A @ X0) @ 
% 1.66/1.84             (k3_xboole_0 @ sk_C @ sk_C)) = (k2_tarski @ sk_A @ X0))
% 1.66/1.84           | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_C))))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['34', '35'])).
% 1.66/1.84  thf(d10_xboole_0, axiom,
% 1.66/1.84    (![A:$i,B:$i]:
% 1.66/1.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.66/1.84  thf('37', plain,
% 1.66/1.84      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.66/1.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.66/1.84  thf('38', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.66/1.84      inference('simplify', [status(thm)], ['37'])).
% 1.66/1.84  thf('39', plain,
% 1.66/1.84      (![X20 : $i, X21 : $i]:
% 1.66/1.84         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 1.66/1.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.66/1.84  thf('40', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.66/1.84      inference('sup-', [status(thm)], ['38', '39'])).
% 1.66/1.84  thf('41', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.84  thf('42', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.66/1.84      inference('sup-', [status(thm)], ['38', '39'])).
% 1.66/1.84  thf('43', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ X0))
% 1.66/1.84             = (k2_tarski @ sk_A @ X0))
% 1.66/1.84           | ~ (r2_hidden @ X0 @ sk_C)))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('demod', [status(thm)], ['36', '40', '41', '42'])).
% 1.66/1.84  thf('44', plain,
% 1.66/1.84      ((((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))
% 1.66/1.84          = (k2_tarski @ sk_A @ sk_B)))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['28', '43'])).
% 1.66/1.84  thf('45', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.84  thf(t100_xboole_1, axiom,
% 1.66/1.84    (![A:$i,B:$i]:
% 1.66/1.84     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.66/1.84  thf('46', plain,
% 1.66/1.84      (![X18 : $i, X19 : $i]:
% 1.66/1.84         ((k4_xboole_0 @ X18 @ X19)
% 1.66/1.84           = (k5_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)))),
% 1.66/1.84      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.84  thf('47', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]:
% 1.66/1.84         ((k4_xboole_0 @ X0 @ X1)
% 1.66/1.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.66/1.84      inference('sup+', [status(thm)], ['45', '46'])).
% 1.66/1.84  thf('48', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 1.66/1.84          = (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 1.66/1.84             (k2_tarski @ sk_A @ sk_B))))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('sup+', [status(thm)], ['44', '47'])).
% 1.66/1.84  thf('49', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.66/1.84      inference('sup-', [status(thm)], ['38', '39'])).
% 1.66/1.84  thf('50', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]:
% 1.66/1.84         ((k4_xboole_0 @ X0 @ X1)
% 1.66/1.84           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.66/1.84      inference('sup+', [status(thm)], ['45', '46'])).
% 1.66/1.84  thf('51', plain,
% 1.66/1.84      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.66/1.84      inference('sup+', [status(thm)], ['49', '50'])).
% 1.66/1.84  thf('52', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.66/1.84      inference('simplify', [status(thm)], ['37'])).
% 1.66/1.84  thf('53', plain,
% 1.66/1.84      (![X15 : $i, X17 : $i]:
% 1.66/1.84         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 1.66/1.84          | ~ (r1_tarski @ X15 @ X17))),
% 1.66/1.84      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.66/1.84  thf('54', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.66/1.84      inference('sup-', [status(thm)], ['52', '53'])).
% 1.66/1.84  thf('55', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.66/1.84      inference('sup+', [status(thm)], ['51', '54'])).
% 1.66/1.84  thf('56', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0)))
% 1.66/1.84         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('demod', [status(thm)], ['48', '55'])).
% 1.66/1.84  thf('57', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) != (k1_xboole_0)))
% 1.66/1.84         <= (~
% 1.66/1.84             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('split', [status(esa)], ['24'])).
% 1.66/1.84  thf('58', plain,
% 1.66/1.84      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.66/1.84         <= (~
% 1.66/1.84             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) & 
% 1.66/1.84             ((r2_hidden @ sk_A @ sk_C)) & 
% 1.66/1.84             ((r2_hidden @ sk_B @ sk_C)))),
% 1.66/1.84      inference('sup-', [status(thm)], ['56', '57'])).
% 1.66/1.84  thf('59', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 1.66/1.84      inference('simplify', [status(thm)], ['58'])).
% 1.66/1.84  thf('60', plain,
% 1.66/1.84      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ((r2_hidden @ sk_A @ sk_C))),
% 1.66/1.84      inference('split', [status(esa)], ['9'])).
% 1.66/1.84  thf('61', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.84         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.66/1.84          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.66/1.84      inference('sup+', [status(thm)], ['2', '4'])).
% 1.66/1.84  thf('62', plain,
% 1.66/1.84      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.66/1.84         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 1.66/1.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.66/1.84  thf('63', plain,
% 1.66/1.84      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.66/1.84         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 1.66/1.84      inference('simplify', [status(thm)], ['62'])).
% 1.66/1.84  thf('64', plain,
% 1.66/1.84      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.66/1.84      inference('sup-', [status(thm)], ['61', '63'])).
% 1.66/1.84  thf('65', plain,
% 1.66/1.84      ((![X0 : $i]:
% 1.66/1.84          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 1.66/1.84           | (r2_hidden @ X0 @ sk_C)))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['17', '21'])).
% 1.66/1.84  thf('66', plain,
% 1.66/1.84      (((r2_hidden @ sk_A @ sk_C))
% 1.66/1.84         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))))),
% 1.66/1.84      inference('sup-', [status(thm)], ['64', '65'])).
% 1.66/1.84  thf('67', plain,
% 1.66/1.84      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 1.66/1.84      inference('split', [status(esa)], ['24'])).
% 1.66/1.84  thf('68', plain,
% 1.66/1.84      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))) | 
% 1.66/1.84       ((r2_hidden @ sk_A @ sk_C))),
% 1.66/1.84      inference('sup-', [status(thm)], ['66', '67'])).
% 1.66/1.84  thf('69', plain, ($false),
% 1.66/1.84      inference('sat_resolution*', [status(thm)],
% 1.66/1.84                ['1', '26', '27', '59', '60', '68'])).
% 1.66/1.84  
% 1.66/1.84  % SZS output end Refutation
% 1.66/1.84  
% 1.68/1.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
