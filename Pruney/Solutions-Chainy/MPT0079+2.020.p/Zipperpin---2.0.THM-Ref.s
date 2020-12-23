%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z4TlG9YRtz

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:59 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 409 expanded)
%              Number of leaves         :   25 ( 142 expanded)
%              Depth                    :   12
%              Number of atoms          :  638 (3231 expanded)
%              Number of equality atoms :   73 ( 317 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t72_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( ( k2_xboole_0 @ A @ B )
            = ( k2_xboole_0 @ C @ D ) )
          & ( r1_xboole_0 @ C @ A )
          & ( r1_xboole_0 @ D @ B ) )
       => ( C = B ) ) ),
    inference('cnf.neg',[status(esa)],[t72_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_D ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_D @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('16',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_D ) @ sk_D )
    = ( k4_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('22',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('23',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','9'])).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('27',plain,
    ( sk_B_1
    = ( k4_xboole_0 @ sk_B_1 @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_D )
    = sk_B_1 ),
    inference(demod,[status(thm)],['20','21','22','27'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D ),
    inference('sup-',[status(thm)],['31','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('44',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('46',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['41','48','49'])).

thf('51',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('53',plain,(
    r1_tarski @ sk_D @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 )
      | ~ ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('55',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_D @ sk_B_1 ) )
    = sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_D
    = ( k4_xboole_0 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['50','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','62'])).

thf('64',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_A ) @ sk_D )
    = ( k4_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['50','61'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('69',plain,(
    sk_D = sk_A ),
    inference('sup+',[status(thm)],['50','61'])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k3_xboole_0 @ X23 @ X24 ) )
      = ( k4_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('74',plain,
    ( sk_C_1
    = ( k4_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['66','67','68','69','74'])).

thf('76',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['63','75'])).

thf('77',plain,(
    sk_C_1 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z4TlG9YRtz
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:27:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.48/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.65  % Solved by: fo/fo7.sh
% 0.48/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.65  % done 658 iterations in 0.194s
% 0.48/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.65  % SZS output start Refutation
% 0.48/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.48/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.48/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.65  thf(t72_xboole_1, conjecture,
% 0.48/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.65     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.48/0.65         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.48/0.65       ( ( C ) = ( B ) ) ))).
% 0.48/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.65        ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.48/0.65            ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.48/0.65          ( ( C ) = ( B ) ) ) )),
% 0.48/0.65    inference('cnf.neg', [status(esa)], [t72_xboole_1])).
% 0.48/0.65  thf('0', plain, ((r1_xboole_0 @ sk_D @ sk_B_1)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf(t4_xboole_0, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.48/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.48/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.48/0.65  thf('1', plain,
% 0.48/0.65      (![X5 : $i, X6 : $i]:
% 0.48/0.65         ((r1_xboole_0 @ X5 @ X6)
% 0.48/0.65          | (r2_hidden @ (sk_C @ X6 @ X5) @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.65  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.65  thf('2', plain,
% 0.48/0.65      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.65  thf('3', plain,
% 0.48/0.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.48/0.65         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.48/0.65          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.48/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.65  thf('4', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.65          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.65  thf('5', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('sup-', [status(thm)], ['1', '4'])).
% 0.48/0.65  thf('6', plain, ((r1_xboole_0 @ sk_B_1 @ sk_D)),
% 0.48/0.65      inference('sup-', [status(thm)], ['0', '5'])).
% 0.48/0.65  thf(t7_xboole_0, axiom,
% 0.48/0.65    (![A:$i]:
% 0.48/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.48/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.48/0.65  thf('7', plain,
% 0.48/0.65      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.48/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.48/0.65  thf('8', plain,
% 0.48/0.65      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.48/0.65         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.48/0.65          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.48/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.48/0.65  thf('9', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.65  thf('10', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.48/0.65  thf('11', plain,
% 0.48/0.65      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.65  thf(t47_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.65  thf('12', plain,
% 0.48/0.65      (![X23 : $i, X24 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.48/0.65           = (k4_xboole_0 @ X23 @ X24))),
% 0.48/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.48/0.65  thf('13', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.65  thf('14', plain,
% 0.48/0.65      (((k4_xboole_0 @ sk_D @ k1_xboole_0) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.48/0.65      inference('sup+', [status(thm)], ['10', '13'])).
% 0.48/0.65  thf(t3_boole, axiom,
% 0.48/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.65  thf('15', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.48/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.65  thf('16', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.65  thf(t39_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.65  thf('17', plain,
% 0.48/0.65      (![X15 : $i, X16 : $i]:
% 0.48/0.65         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 0.48/0.65           = (k2_xboole_0 @ X15 @ X16))),
% 0.48/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.48/0.65  thf(t40_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.48/0.65  thf('18', plain,
% 0.48/0.65      (![X18 : $i, X19 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.48/0.65           = (k4_xboole_0 @ X18 @ X19))),
% 0.48/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.65  thf('19', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.65           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.48/0.65      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.65  thf('20', plain,
% 0.48/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_D) @ sk_D)
% 0.48/0.65         = (k4_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ sk_D @ sk_B_1)))),
% 0.48/0.65      inference('sup+', [status(thm)], ['16', '19'])).
% 0.48/0.65  thf('21', plain,
% 0.48/0.65      (![X18 : $i, X19 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.48/0.65           = (k4_xboole_0 @ X18 @ X19))),
% 0.48/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.65  thf('22', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.65  thf('23', plain, (((k3_xboole_0 @ sk_B_1 @ sk_D) = (k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['6', '9'])).
% 0.48/0.65  thf('24', plain,
% 0.48/0.65      (![X23 : $i, X24 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.48/0.65           = (k4_xboole_0 @ X23 @ X24))),
% 0.48/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.48/0.65  thf('25', plain,
% 0.48/0.65      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.48/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.48/0.65  thf('26', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.48/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.65  thf('27', plain, (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['25', '26'])).
% 0.48/0.65  thf('28', plain, (((k4_xboole_0 @ sk_B_1 @ sk_D) = (sk_B_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['20', '21', '22', '27'])).
% 0.48/0.65  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.65  thf('29', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf(t7_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.48/0.65  thf('30', plain,
% 0.48/0.65      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 0.48/0.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.48/0.65  thf('31', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.48/0.65      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.65  thf('32', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_A @ sk_B_1) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('33', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('34', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.48/0.65  thf(t43_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i,C:$i]:
% 0.48/0.65     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.48/0.65       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.48/0.65  thf('35', plain,
% 0.48/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.48/0.65         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.48/0.65          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.48/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.48/0.65  thf('36', plain,
% 0.48/0.65      (![X0 : $i]:
% 0.48/0.65         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_A))
% 0.48/0.65          | (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_D))),
% 0.48/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.65  thf('37', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D)),
% 0.48/0.65      inference('sup-', [status(thm)], ['31', '36'])).
% 0.48/0.65  thf(t12_xboole_1, axiom,
% 0.48/0.65    (![A:$i,B:$i]:
% 0.48/0.65     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.48/0.65  thf('38', plain,
% 0.48/0.65      (![X13 : $i, X14 : $i]:
% 0.48/0.65         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.48/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.48/0.65  thf('39', plain,
% 0.48/0.65      (((k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_C_1) @ sk_D) = (sk_D))),
% 0.48/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.65  thf('40', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('41', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_D @ (k4_xboole_0 @ sk_A @ sk_C_1)) = (sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.65  thf('42', plain, ((r1_xboole_0 @ sk_C_1 @ sk_A)),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('43', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.65  thf('44', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.65  thf('45', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.48/0.65           = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.65  thf('46', plain,
% 0.48/0.65      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.48/0.65      inference('sup+', [status(thm)], ['44', '45'])).
% 0.48/0.65  thf('47', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.48/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.65  thf('48', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.48/0.65  thf('49', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('50', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['41', '48', '49'])).
% 0.48/0.65  thf('51', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.48/0.65  thf('52', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.48/0.65      inference('sup+', [status(thm)], ['29', '30'])).
% 0.48/0.65  thf('53', plain, ((r1_tarski @ sk_D @ (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.48/0.65      inference('sup+', [status(thm)], ['51', '52'])).
% 0.48/0.65  thf('54', plain,
% 0.48/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.48/0.65         ((r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22)
% 0.48/0.65          | ~ (r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22)))),
% 0.48/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.48/0.65  thf('55', plain, ((r1_tarski @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A)),
% 0.48/0.65      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.65  thf('56', plain,
% 0.48/0.65      (![X13 : $i, X14 : $i]:
% 0.48/0.65         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.48/0.65      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.48/0.65  thf('57', plain,
% 0.48/0.65      (((k2_xboole_0 @ (k4_xboole_0 @ sk_D @ sk_B_1) @ sk_A) = (sk_A))),
% 0.48/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.48/0.65  thf('58', plain,
% 0.48/0.65      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.65      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.65  thf('59', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_D @ sk_B_1)) = (sk_A))),
% 0.48/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.48/0.65  thf('60', plain, (((sk_D) = (k4_xboole_0 @ sk_D @ sk_B_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['14', '15'])).
% 0.48/0.65  thf('61', plain, (((k2_xboole_0 @ sk_A @ sk_D) = (sk_A))),
% 0.48/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.48/0.65  thf('62', plain, (((sk_D) = (sk_A))),
% 0.48/0.65      inference('sup+', [status(thm)], ['50', '61'])).
% 0.48/0.65  thf('63', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['28', '62'])).
% 0.48/0.65  thf('64', plain,
% 0.48/0.65      (((k2_xboole_0 @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.65      inference('demod', [status(thm)], ['32', '33'])).
% 0.48/0.65  thf('65', plain,
% 0.48/0.65      (![X18 : $i, X19 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.48/0.65           = (k4_xboole_0 @ X18 @ X19))),
% 0.48/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.65  thf('66', plain,
% 0.48/0.65      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_A) @ sk_D)
% 0.48/0.65         = (k4_xboole_0 @ sk_C_1 @ sk_D))),
% 0.48/0.65      inference('sup+', [status(thm)], ['64', '65'])).
% 0.48/0.65  thf('67', plain, (((sk_D) = (sk_A))),
% 0.48/0.65      inference('sup+', [status(thm)], ['50', '61'])).
% 0.48/0.65  thf('68', plain,
% 0.48/0.65      (![X18 : $i, X19 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 0.48/0.65           = (k4_xboole_0 @ X18 @ X19))),
% 0.48/0.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.48/0.65  thf('69', plain, (((sk_D) = (sk_A))),
% 0.48/0.65      inference('sup+', [status(thm)], ['50', '61'])).
% 0.48/0.65  thf('70', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (k1_xboole_0))),
% 0.48/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.48/0.65  thf('71', plain,
% 0.48/0.65      (![X23 : $i, X24 : $i]:
% 0.48/0.65         ((k4_xboole_0 @ X23 @ (k3_xboole_0 @ X23 @ X24))
% 0.48/0.65           = (k4_xboole_0 @ X23 @ X24))),
% 0.48/0.65      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.48/0.65  thf('72', plain,
% 0.48/0.65      (((k4_xboole_0 @ sk_C_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.48/0.65      inference('sup+', [status(thm)], ['70', '71'])).
% 0.48/0.65  thf('73', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 0.48/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.65  thf('74', plain, (((sk_C_1) = (k4_xboole_0 @ sk_C_1 @ sk_A))),
% 0.48/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.48/0.65  thf('75', plain, (((k4_xboole_0 @ sk_B_1 @ sk_A) = (sk_C_1))),
% 0.48/0.65      inference('demod', [status(thm)], ['66', '67', '68', '69', '74'])).
% 0.48/0.65  thf('76', plain, (((sk_B_1) = (sk_C_1))),
% 0.48/0.65      inference('sup+', [status(thm)], ['63', '75'])).
% 0.48/0.65  thf('77', plain, (((sk_C_1) != (sk_B_1))),
% 0.48/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.65  thf('78', plain, ($false),
% 0.48/0.65      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.48/0.65  
% 0.48/0.65  % SZS output end Refutation
% 0.48/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
