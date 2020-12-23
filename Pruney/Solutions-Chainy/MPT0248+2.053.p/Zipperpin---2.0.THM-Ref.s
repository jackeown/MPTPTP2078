%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v9dm5AaOI2

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 5.36s
% Output     : Refutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 196 expanded)
%              Number of leaves         :   25 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  695 (2147 expanded)
%              Number of equality atoms :  112 ( 436 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','21','22'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','25'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('27',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52
        = ( k1_tarski @ X51 ) )
      | ( X52 = k1_xboole_0 )
      | ~ ( r1_tarski @ X52 @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('28',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('36',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X51: $i,X52: $i] :
      ( ( X52
        = ( k1_tarski @ X51 ) )
      | ( X52 = k1_xboole_0 )
      | ~ ( r1_tarski @ X52 @ ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('38',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('44',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','33','45'])).

thf('47',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','46'])).

thf('48',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('49',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('56',plain,(
    ! [X15: $i] :
      ( r1_xboole_0 @ X15 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('57',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','65'])).

thf('67',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['49','66'])).

thf('68',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','46'])).

thf('69',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('71',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','47','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v9dm5AaOI2
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.36/5.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.36/5.54  % Solved by: fo/fo7.sh
% 5.36/5.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.36/5.54  % done 1539 iterations in 5.086s
% 5.36/5.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.36/5.54  % SZS output start Refutation
% 5.36/5.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 5.36/5.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.36/5.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.36/5.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.36/5.54  thf(sk_B_type, type, sk_B: $i > $i).
% 5.36/5.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.36/5.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.36/5.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.36/5.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 5.36/5.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.36/5.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.36/5.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.36/5.54  thf(sk_A_type, type, sk_A: $i).
% 5.36/5.54  thf(t43_zfmisc_1, conjecture,
% 5.36/5.54    (![A:$i,B:$i,C:$i]:
% 5.36/5.54     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 5.36/5.54          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 5.36/5.54          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 5.36/5.54          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 5.36/5.54  thf(zf_stmt_0, negated_conjecture,
% 5.36/5.54    (~( ![A:$i,B:$i,C:$i]:
% 5.36/5.54        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 5.36/5.54             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 5.36/5.54             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 5.36/5.54             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 5.36/5.54    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 5.36/5.54  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf(commutativity_k3_xboole_0, axiom,
% 5.36/5.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 5.36/5.54  thf('1', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.36/5.54  thf(t100_xboole_1, axiom,
% 5.36/5.54    (![A:$i,B:$i]:
% 5.36/5.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.36/5.54  thf('2', plain,
% 5.36/5.54      (![X12 : $i, X13 : $i]:
% 5.36/5.54         ((k4_xboole_0 @ X12 @ X13)
% 5.36/5.54           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.54  thf('3', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         ((k4_xboole_0 @ X0 @ X1)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['1', '2'])).
% 5.36/5.54  thf('4', plain,
% 5.36/5.54      (![X12 : $i, X13 : $i]:
% 5.36/5.54         ((k4_xboole_0 @ X12 @ X13)
% 5.36/5.54           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.54  thf(commutativity_k5_xboole_0, axiom,
% 5.36/5.54    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 5.36/5.54  thf('5', plain,
% 5.36/5.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.36/5.54  thf(t91_xboole_1, axiom,
% 5.36/5.54    (![A:$i,B:$i,C:$i]:
% 5.36/5.54     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 5.36/5.54       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 5.36/5.54  thf('6', plain,
% 5.36/5.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 5.36/5.54           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.36/5.54  thf('7', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X2)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X2)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['5', '6'])).
% 5.36/5.54  thf('8', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 5.36/5.54           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X1 @ X2)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['4', '7'])).
% 5.36/5.54  thf('9', plain,
% 5.36/5.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 5.36/5.54           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.36/5.54  thf('10', plain,
% 5.36/5.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.36/5.54  thf('11', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 5.36/5.54           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['9', '10'])).
% 5.36/5.54  thf('12', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 5.36/5.54           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.36/5.54      inference('demod', [status(thm)], ['8', '11'])).
% 5.36/5.54  thf('13', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['3', '12'])).
% 5.36/5.54  thf('14', plain,
% 5.36/5.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.36/5.54  thf('15', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.36/5.54  thf(t94_xboole_1, axiom,
% 5.36/5.54    (![A:$i,B:$i]:
% 5.36/5.54     ( ( k2_xboole_0 @ A @ B ) =
% 5.36/5.54       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 5.36/5.54  thf('16', plain,
% 5.36/5.54      (![X21 : $i, X22 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X21 @ X22)
% 5.36/5.54           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 5.36/5.54              (k3_xboole_0 @ X21 @ X22)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t94_xboole_1])).
% 5.36/5.54  thf('17', plain,
% 5.36/5.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 5.36/5.54         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 5.36/5.54           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t91_xboole_1])).
% 5.36/5.54  thf('18', plain,
% 5.36/5.54      (![X21 : $i, X22 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X21 @ X22)
% 5.36/5.54           = (k5_xboole_0 @ X21 @ 
% 5.36/5.54              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 5.36/5.54      inference('demod', [status(thm)], ['16', '17'])).
% 5.36/5.54  thf('19', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X0 @ X1)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 5.36/5.54      inference('sup+', [status(thm)], ['15', '18'])).
% 5.36/5.54  thf('20', plain,
% 5.36/5.54      (![X12 : $i, X13 : $i]:
% 5.36/5.54         ((k4_xboole_0 @ X12 @ X13)
% 5.36/5.54           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 5.36/5.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 5.36/5.54  thf('21', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X0 @ X1)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.36/5.54      inference('demod', [status(thm)], ['19', '20'])).
% 5.36/5.54  thf('22', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X0 @ X1)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 5.36/5.54      inference('demod', [status(thm)], ['19', '20'])).
% 5.36/5.54  thf('23', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 5.36/5.54      inference('demod', [status(thm)], ['13', '14', '21', '22'])).
% 5.36/5.54  thf(t7_xboole_1, axiom,
% 5.36/5.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 5.36/5.54  thf('24', plain,
% 5.36/5.54      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 5.36/5.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.36/5.54  thf('25', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 5.36/5.54      inference('sup+', [status(thm)], ['23', '24'])).
% 5.36/5.54  thf('26', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 5.36/5.54      inference('sup+', [status(thm)], ['0', '25'])).
% 5.36/5.54  thf(l3_zfmisc_1, axiom,
% 5.36/5.54    (![A:$i,B:$i]:
% 5.36/5.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 5.36/5.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 5.36/5.54  thf('27', plain,
% 5.36/5.54      (![X51 : $i, X52 : $i]:
% 5.36/5.54         (((X52) = (k1_tarski @ X51))
% 5.36/5.54          | ((X52) = (k1_xboole_0))
% 5.36/5.54          | ~ (r1_tarski @ X52 @ (k1_tarski @ X51)))),
% 5.36/5.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 5.36/5.54  thf('28', plain,
% 5.36/5.54      ((((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('sup-', [status(thm)], ['26', '27'])).
% 5.36/5.54  thf('29', plain,
% 5.36/5.54      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf('30', plain,
% 5.36/5.54      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 5.36/5.54         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('split', [status(esa)], ['29'])).
% 5.36/5.54  thf('31', plain,
% 5.36/5.54      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 5.36/5.54      inference('split', [status(esa)], ['29'])).
% 5.36/5.54  thf('32', plain,
% 5.36/5.54      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf('33', plain,
% 5.36/5.54      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 5.36/5.54       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('split', [status(esa)], ['32'])).
% 5.36/5.54  thf('34', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf('35', plain,
% 5.36/5.54      (![X16 : $i, X17 : $i]: (r1_tarski @ X16 @ (k2_xboole_0 @ X16 @ X17))),
% 5.36/5.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 5.36/5.54  thf('36', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 5.36/5.54      inference('sup+', [status(thm)], ['34', '35'])).
% 5.36/5.54  thf('37', plain,
% 5.36/5.54      (![X51 : $i, X52 : $i]:
% 5.36/5.54         (((X52) = (k1_tarski @ X51))
% 5.36/5.54          | ((X52) = (k1_xboole_0))
% 5.36/5.54          | ~ (r1_tarski @ X52 @ (k1_tarski @ X51)))),
% 5.36/5.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 5.36/5.54  thf('38', plain,
% 5.36/5.54      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('sup-', [status(thm)], ['36', '37'])).
% 5.36/5.54  thf('39', plain,
% 5.36/5.54      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf('40', plain,
% 5.36/5.54      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 5.36/5.54         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('split', [status(esa)], ['39'])).
% 5.36/5.54  thf('41', plain,
% 5.36/5.54      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 5.36/5.54         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('sup-', [status(thm)], ['38', '40'])).
% 5.36/5.54  thf('42', plain,
% 5.36/5.54      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('simplify', [status(thm)], ['41'])).
% 5.36/5.54  thf('43', plain,
% 5.36/5.54      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 5.36/5.54      inference('split', [status(esa)], ['29'])).
% 5.36/5.54  thf('44', plain,
% 5.36/5.54      ((((sk_B_1) != (sk_B_1)))
% 5.36/5.54         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 5.36/5.54             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('sup-', [status(thm)], ['42', '43'])).
% 5.36/5.54  thf('45', plain,
% 5.36/5.54      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('simplify', [status(thm)], ['44'])).
% 5.36/5.54  thf('46', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('sat_resolution*', [status(thm)], ['31', '33', '45'])).
% 5.36/5.54  thf('47', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 5.36/5.54      inference('simpl_trail', [status(thm)], ['30', '46'])).
% 5.36/5.54  thf('48', plain,
% 5.36/5.54      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 5.36/5.54      inference('split', [status(esa)], ['39'])).
% 5.36/5.54  thf('49', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 5.36/5.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.36/5.54  thf('50', plain,
% 5.36/5.54      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('simplify', [status(thm)], ['41'])).
% 5.36/5.54  thf('51', plain,
% 5.36/5.54      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 5.36/5.54  thf(t5_boole, axiom,
% 5.36/5.54    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.36/5.54  thf('52', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 5.36/5.54      inference('cnf', [status(esa)], [t5_boole])).
% 5.36/5.54  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.36/5.54      inference('sup+', [status(thm)], ['51', '52'])).
% 5.36/5.54  thf('54', plain,
% 5.36/5.54      (![X21 : $i, X22 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ X21 @ X22)
% 5.36/5.54           = (k5_xboole_0 @ X21 @ 
% 5.36/5.54              (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X21 @ X22))))),
% 5.36/5.54      inference('demod', [status(thm)], ['16', '17'])).
% 5.36/5.54  thf('55', plain,
% 5.36/5.54      (![X0 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 5.36/5.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 5.36/5.54      inference('sup+', [status(thm)], ['53', '54'])).
% 5.36/5.54  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 5.36/5.54  thf('56', plain, (![X15 : $i]: (r1_xboole_0 @ X15 @ k1_xboole_0)),
% 5.36/5.54      inference('cnf', [status(esa)], [t65_xboole_1])).
% 5.36/5.54  thf(t7_xboole_0, axiom,
% 5.36/5.54    (![A:$i]:
% 5.36/5.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.36/5.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 5.36/5.54  thf('57', plain,
% 5.36/5.54      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 5.36/5.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.36/5.54  thf(t4_xboole_0, axiom,
% 5.36/5.54    (![A:$i,B:$i]:
% 5.36/5.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 5.36/5.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.36/5.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.36/5.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 5.36/5.54  thf('58', plain,
% 5.36/5.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 5.36/5.54         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 5.36/5.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 5.36/5.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 5.36/5.54  thf('59', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]:
% 5.36/5.54         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 5.36/5.54      inference('sup-', [status(thm)], ['57', '58'])).
% 5.36/5.54  thf('60', plain,
% 5.36/5.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 5.36/5.54      inference('sup-', [status(thm)], ['56', '59'])).
% 5.36/5.54  thf('61', plain,
% 5.36/5.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 5.36/5.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 5.36/5.54  thf('62', plain,
% 5.36/5.54      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 5.36/5.54      inference('sup+', [status(thm)], ['60', '61'])).
% 5.36/5.54  thf('63', plain,
% 5.36/5.54      (![X0 : $i]:
% 5.36/5.54         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 5.36/5.54      inference('demod', [status(thm)], ['55', '62'])).
% 5.36/5.54  thf('64', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 5.36/5.54      inference('cnf', [status(esa)], [t5_boole])).
% 5.36/5.54  thf('65', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 5.36/5.54      inference('sup+', [status(thm)], ['63', '64'])).
% 5.36/5.54  thf('66', plain,
% 5.36/5.54      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 5.36/5.54         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('sup+', [status(thm)], ['50', '65'])).
% 5.36/5.54  thf('67', plain,
% 5.36/5.54      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 5.36/5.54         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 5.36/5.54      inference('sup+', [status(thm)], ['49', '66'])).
% 5.36/5.54  thf('68', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 5.36/5.54      inference('simpl_trail', [status(thm)], ['30', '46'])).
% 5.36/5.54  thf('69', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 5.36/5.54  thf('70', plain,
% 5.36/5.54      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 5.36/5.54      inference('split', [status(esa)], ['39'])).
% 5.36/5.54  thf('71', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 5.36/5.54      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 5.36/5.54  thf('72', plain, (((sk_C_1) != (k1_xboole_0))),
% 5.36/5.54      inference('simpl_trail', [status(thm)], ['48', '71'])).
% 5.36/5.54  thf('73', plain, ($false),
% 5.36/5.54      inference('simplify_reflect-', [status(thm)], ['28', '47', '72'])).
% 5.36/5.54  
% 5.36/5.54  % SZS output end Refutation
% 5.36/5.54  
% 5.36/5.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
