%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xU1TA5wb8L

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  216 (1056 expanded)
%              Number of leaves         :   29 ( 336 expanded)
%              Depth                    :   30
%              Number of atoms          : 1628 (9781 expanded)
%              Number of equality atoms :  259 (1637 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_tarski @ X55 @ ( k1_tarski @ X56 ) )
      | ( X55 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('35',plain,(
    ! [X56: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X56 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('63',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('64',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('81',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('82',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k3_tarski @ ( k1_tarski @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','84'])).

thf('86',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('87',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('91',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','101'])).

thf('103',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','106'])).

thf('108',plain,(
    ! [X56: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X56 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('109',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0
        = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('115',plain,(
    ! [X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('116',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','117'])).

thf('119',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('120',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X56: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X56 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('122',plain,(
    r1_tarski @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('124',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('127',plain,
    ( ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('129',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('131',plain,
    ( ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
      = sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X14 @ X15 ) @ ( k2_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ sk_C ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('136',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('137',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['134','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('140',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['140','145'])).

thf('147',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('148',plain,
    ( ( sk_C = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('150',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('151',plain,
    ( ( sk_C != sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['148','151'])).

thf('153',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('154',plain,
    ( ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B @ sk_C )
      = ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('157',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ k1_xboole_0 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( sk_C
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['131','157'])).

thf('159',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('160',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('163',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X17 @ X18 ) @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('168',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['158','161','168'])).

thf('170',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('172',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('175',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['113','117'])).

thf('176',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    sk_C
 != ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('178',plain,
    ( ( sk_C != sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('181',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['179','180'])).

thf('182',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['173','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['118','182'])).

thf('184',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['24','183'])).

thf('185',plain,(
    $false ),
    inference(simplify,[status(thm)],['184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xU1TA5wb8L
% 0.14/0.37  % Computer   : n002.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 09:26:22 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.45/1.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.45/1.64  % Solved by: fo/fo7.sh
% 1.45/1.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.45/1.64  % done 4566 iterations in 1.190s
% 1.45/1.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.45/1.64  % SZS output start Refutation
% 1.45/1.64  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(sk_B_type, type, sk_B: $i).
% 1.45/1.64  thf(sk_C_type, type, sk_C: $i).
% 1.45/1.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.45/1.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.45/1.64  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.45/1.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.45/1.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(sk_A_type, type, sk_A: $i).
% 1.45/1.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.45/1.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.45/1.64  thf(t43_zfmisc_1, conjecture,
% 1.45/1.64    (![A:$i,B:$i,C:$i]:
% 1.45/1.64     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.45/1.64          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.45/1.64          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.45/1.64          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.45/1.64  thf(zf_stmt_0, negated_conjecture,
% 1.45/1.64    (~( ![A:$i,B:$i,C:$i]:
% 1.45/1.64        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.45/1.64             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.45/1.64             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.45/1.64             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.45/1.64    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.45/1.64  thf('0', plain,
% 1.45/1.64      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('1', plain,
% 1.45/1.64      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('split', [status(esa)], ['0'])).
% 1.45/1.64  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('3', plain,
% 1.45/1.64      ((((sk_C) != (k2_xboole_0 @ sk_B @ sk_C)))
% 1.45/1.64         <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('demod', [status(thm)], ['1', '2'])).
% 1.45/1.64  thf('4', plain,
% 1.45/1.64      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.45/1.64      inference('split', [status(esa)], ['0'])).
% 1.45/1.64  thf('5', plain,
% 1.45/1.64      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('6', plain,
% 1.45/1.64      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('split', [status(esa)], ['5'])).
% 1.45/1.64  thf(t7_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.64  thf('7', plain,
% 1.45/1.64      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.45/1.64      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.45/1.64  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf(l3_zfmisc_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.45/1.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.45/1.64  thf('9', plain,
% 1.45/1.64      (![X54 : $i, X55 : $i]:
% 1.45/1.64         (((X55) = (k1_tarski @ X54))
% 1.45/1.64          | ((X55) = (k1_xboole_0))
% 1.45/1.64          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 1.45/1.64      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.45/1.64  thf('10', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['8', '9'])).
% 1.45/1.64  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('12', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.45/1.64          | ((X0) = (k1_xboole_0))
% 1.45/1.64          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.45/1.64      inference('demod', [status(thm)], ['10', '11'])).
% 1.45/1.64  thf('13', plain,
% 1.45/1.64      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.64      inference('sup-', [status(thm)], ['7', '12'])).
% 1.45/1.64  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('15', plain,
% 1.45/1.64      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 1.45/1.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.64  thf('16', plain,
% 1.45/1.64      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('split', [status(esa)], ['15'])).
% 1.45/1.64  thf('17', plain,
% 1.45/1.64      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C)))
% 1.45/1.64         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['14', '16'])).
% 1.45/1.64  thf('18', plain,
% 1.45/1.64      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.45/1.64         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['13', '17'])).
% 1.45/1.64  thf('19', plain,
% 1.45/1.64      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('simplify', [status(thm)], ['18'])).
% 1.45/1.64  thf('20', plain,
% 1.45/1.64      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.45/1.64      inference('split', [status(esa)], ['0'])).
% 1.45/1.64  thf('21', plain,
% 1.45/1.64      ((((sk_B) != (sk_B)))
% 1.45/1.64         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.64      inference('sup-', [status(thm)], ['19', '20'])).
% 1.45/1.64  thf('22', plain,
% 1.45/1.64      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('simplify', [status(thm)], ['21'])).
% 1.45/1.64  thf('23', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 1.45/1.64      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 1.45/1.64  thf('24', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.64      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.45/1.64  thf(t100_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.45/1.64  thf('25', plain,
% 1.45/1.64      (![X10 : $i, X11 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ X10 @ X11)
% 1.45/1.64           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.45/1.64      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.64  thf(commutativity_k5_xboole_0, axiom,
% 1.45/1.64    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.45/1.64  thf('26', plain,
% 1.45/1.64      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.64      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.64  thf(t5_boole, axiom,
% 1.45/1.64    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.45/1.64  thf('27', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.45/1.64      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.64  thf('28', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['26', '27'])).
% 1.45/1.64  thf('29', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.64      inference('sup+', [status(thm)], ['25', '28'])).
% 1.45/1.64  thf(l98_xboole_1, axiom,
% 1.45/1.64    (![A:$i,B:$i]:
% 1.45/1.64     ( ( k5_xboole_0 @ A @ B ) =
% 1.45/1.64       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.45/1.64  thf('30', plain,
% 1.45/1.64      (![X8 : $i, X9 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.64           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.64      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.64  thf('31', plain,
% 1.45/1.64      (![X0 : $i]:
% 1.45/1.64         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 1.45/1.65              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['29', '30'])).
% 1.45/1.65  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['26', '27'])).
% 1.45/1.65  thf('33', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ 
% 1.45/1.65              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['31', '32'])).
% 1.45/1.65  thf('34', plain,
% 1.45/1.65      (![X55 : $i, X56 : $i]:
% 1.45/1.65         ((r1_tarski @ X55 @ (k1_tarski @ X56)) | ((X55) != (k1_xboole_0)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.45/1.65  thf('35', plain,
% 1.45/1.65      (![X56 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X56))),
% 1.45/1.65      inference('simplify', [status(thm)], ['34'])).
% 1.45/1.65  thf(t28_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.45/1.65  thf('36', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('37', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['35', '36'])).
% 1.45/1.65  thf('38', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('39', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 1.45/1.65              k1_xboole_0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['37', '38'])).
% 1.45/1.65  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['26', '27'])).
% 1.45/1.65  thf('41', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k1_tarski @ X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) @ 
% 1.45/1.65              k1_xboole_0))),
% 1.45/1.65      inference('demod', [status(thm)], ['39', '40'])).
% 1.45/1.65  thf('42', plain,
% 1.45/1.65      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.45/1.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.45/1.65  thf(l32_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.45/1.65  thf('43', plain,
% 1.45/1.65      (![X5 : $i, X7 : $i]:
% 1.45/1.65         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.45/1.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.45/1.65  thf('44', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['42', '43'])).
% 1.45/1.65  thf('45', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['25', '28'])).
% 1.45/1.65  thf(commutativity_k3_xboole_0, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.45/1.65  thf('46', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.65  thf('47', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['45', '46'])).
% 1.45/1.65  thf('48', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('49', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.45/1.65              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['47', '48'])).
% 1.45/1.65  thf('50', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.45/1.65      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.65  thf('51', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.45/1.65              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['49', '50'])).
% 1.45/1.65  thf('52', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.45/1.65           = (k4_xboole_0 @ 
% 1.45/1.65              (k2_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) @ 
% 1.45/1.65              k1_xboole_0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['44', '51'])).
% 1.45/1.65  thf(t40_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('53', plain,
% 1.45/1.65      (![X17 : $i, X18 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 1.45/1.65           = (k4_xboole_0 @ X17 @ X18))),
% 1.45/1.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.45/1.65  thf('54', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 1.45/1.65      inference('demod', [status(thm)], ['52', '53'])).
% 1.45/1.65  thf('55', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k1_tarski @ X0) = (k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['41', '54'])).
% 1.45/1.65  thf('56', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['25', '28'])).
% 1.45/1.65  thf(t29_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 1.45/1.65  thf('57', plain,
% 1.45/1.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.65         (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ (k2_xboole_0 @ X14 @ X16))),
% 1.45/1.65      inference('cnf', [status(esa)], [t29_xboole_1])).
% 1.45/1.65  thf('58', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ 
% 1.45/1.65          (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 1.45/1.65      inference('sup+', [status(thm)], ['56', '57'])).
% 1.45/1.65  thf('59', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X1) @ (k1_tarski @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['55', '58'])).
% 1.45/1.65  thf('60', plain,
% 1.45/1.65      (![X54 : $i, X55 : $i]:
% 1.45/1.65         (((X55) = (k1_tarski @ X54))
% 1.45/1.65          | ((X55) = (k1_xboole_0))
% 1.45/1.65          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.45/1.65  thf('61', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 1.45/1.65          | ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_tarski @ X0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['59', '60'])).
% 1.45/1.65  thf('62', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['25', '28'])).
% 1.45/1.65  thf(t69_enumset1, axiom,
% 1.45/1.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.45/1.65  thf('63', plain,
% 1.45/1.65      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 1.45/1.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.45/1.65  thf(l51_zfmisc_1, axiom,
% 1.45/1.65    (![A:$i,B:$i]:
% 1.45/1.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.45/1.65  thf('64', plain,
% 1.45/1.65      (![X57 : $i, X58 : $i]:
% 1.45/1.65         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 1.45/1.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.45/1.65  thf('65', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['63', '64'])).
% 1.45/1.65  thf('66', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['63', '64'])).
% 1.45/1.65  thf('67', plain,
% 1.45/1.65      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.45/1.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.45/1.65  thf('68', plain,
% 1.45/1.65      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_tarski @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['66', '67'])).
% 1.45/1.65  thf('69', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('70', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (X0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['68', '69'])).
% 1.45/1.65  thf('71', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.65  thf('72', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('73', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ X1)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['71', '72'])).
% 1.45/1.65  thf('74', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0)
% 1.45/1.65           = (k4_xboole_0 @ 
% 1.45/1.65              (k2_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0) @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['70', '73'])).
% 1.45/1.65  thf('75', plain,
% 1.45/1.65      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.45/1.65  thf('76', plain,
% 1.45/1.65      (![X17 : $i, X18 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 1.45/1.65           = (k4_xboole_0 @ X17 @ X18))),
% 1.45/1.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.45/1.65  thf('77', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0)))
% 1.45/1.65           = (k4_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.45/1.65  thf('78', plain,
% 1.45/1.65      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['63', '64'])).
% 1.45/1.65  thf('79', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('80', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ X0)
% 1.45/1.65           = (k4_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ 
% 1.45/1.65              (k3_xboole_0 @ X0 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['78', '79'])).
% 1.45/1.65  thf(t92_xboole_1, axiom,
% 1.45/1.65    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.45/1.65  thf('81', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 1.45/1.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.45/1.65  thf(idempotence_k3_xboole_0, axiom,
% 1.45/1.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.45/1.65  thf('82', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.45/1.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.45/1.65  thf('83', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k1_xboole_0) = (k4_xboole_0 @ (k3_tarski @ (k1_tarski @ X0)) @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.45/1.65  thf('84', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ (k3_tarski @ (k1_tarski @ X0))) = (k1_xboole_0))),
% 1.45/1.65      inference('demod', [status(thm)], ['77', '83'])).
% 1.45/1.65  thf('85', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['65', '84'])).
% 1.45/1.65  thf('86', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('87', plain,
% 1.45/1.65      (![X5 : $i, X6 : $i]:
% 1.45/1.65         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.45/1.65  thf('88', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (((k5_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 1.45/1.65          | (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['86', '87'])).
% 1.45/1.65  thf('89', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.65          | (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ 
% 1.45/1.65             (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0))))),
% 1.45/1.65      inference('sup-', [status(thm)], ['85', '88'])).
% 1.45/1.65  thf('90', plain,
% 1.45/1.65      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.45/1.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.45/1.65  thf('91', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('92', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.45/1.65      inference('sup-', [status(thm)], ['90', '91'])).
% 1.45/1.65  thf('93', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         (((k1_xboole_0) != (k1_xboole_0))
% 1.45/1.65          | (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['89', '92'])).
% 1.45/1.65  thf('94', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         (r1_tarski @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ X0)),
% 1.45/1.65      inference('simplify', [status(thm)], ['93'])).
% 1.45/1.65  thf('95', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('96', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)) @ X0)
% 1.45/1.65           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['94', '95'])).
% 1.45/1.65  thf('97', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.65  thf('98', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.45/1.65      inference('sup-', [status(thm)], ['90', '91'])).
% 1.45/1.65  thf('99', plain,
% 1.45/1.65      (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.45/1.65  thf('100', plain,
% 1.45/1.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.65         (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ (k2_xboole_0 @ X14 @ X16))),
% 1.45/1.65      inference('cnf', [status(esa)], [t29_xboole_1])).
% 1.45/1.65  thf('101', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.45/1.65      inference('sup+', [status(thm)], ['99', '100'])).
% 1.45/1.65  thf('102', plain,
% 1.45/1.65      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 1.45/1.65      inference('sup+', [status(thm)], ['62', '101'])).
% 1.45/1.65  thf('103', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('104', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 1.45/1.65           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['102', '103'])).
% 1.45/1.65  thf('105', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['45', '46'])).
% 1.45/1.65  thf('106', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 1.45/1.65           = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['104', '105'])).
% 1.45/1.65  thf('107', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         (((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 1.45/1.65            = (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.45/1.65          | ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['61', '106'])).
% 1.45/1.65  thf('108', plain,
% 1.45/1.65      (![X56 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X56))),
% 1.45/1.65      inference('simplify', [status(thm)], ['34'])).
% 1.45/1.65  thf('109', plain,
% 1.45/1.65      (![X5 : $i, X7 : $i]:
% 1.45/1.65         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 1.45/1.65      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.45/1.65  thf('110', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['108', '109'])).
% 1.45/1.65  thf('111', plain,
% 1.45/1.65      (![X1 : $i]:
% 1.45/1.65         (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1))
% 1.45/1.65          | ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['107', '110'])).
% 1.45/1.65  thf('112', plain,
% 1.45/1.65      (![X1 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 1.45/1.65      inference('simplify', [status(thm)], ['111'])).
% 1.45/1.65  thf('113', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((X0) = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 1.45/1.65      inference('demod', [status(thm)], ['33', '112'])).
% 1.45/1.65  thf('114', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ 
% 1.45/1.65              (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['49', '50'])).
% 1.45/1.65  thf('115', plain,
% 1.45/1.65      (![X1 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 1.45/1.65      inference('simplify', [status(thm)], ['111'])).
% 1.45/1.65  thf('116', plain,
% 1.45/1.65      (![X17 : $i, X18 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 1.45/1.65           = (k4_xboole_0 @ X17 @ X18))),
% 1.45/1.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.45/1.65  thf('117', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.45/1.65      inference('demod', [status(thm)], ['114', '115', '116'])).
% 1.45/1.65  thf('118', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['113', '117'])).
% 1.45/1.65  thf('119', plain,
% 1.45/1.65      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['7', '12'])).
% 1.45/1.65  thf('120', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.45/1.65  thf('121', plain,
% 1.45/1.65      (![X56 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X56))),
% 1.45/1.65      inference('simplify', [status(thm)], ['34'])).
% 1.45/1.65  thf('122', plain, ((r1_tarski @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.65      inference('sup+', [status(thm)], ['120', '121'])).
% 1.45/1.65  thf('123', plain,
% 1.45/1.65      (![X12 : $i, X13 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 1.45/1.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.45/1.65  thf('124', plain,
% 1.45/1.65      (((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.45/1.65         = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['122', '123'])).
% 1.45/1.65  thf('125', plain,
% 1.45/1.65      ((((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['119', '124'])).
% 1.45/1.65  thf('126', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.45/1.65      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.45/1.65  thf('127', plain,
% 1.45/1.65      ((((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['125', '126'])).
% 1.45/1.65  thf('128', plain,
% 1.45/1.65      (![X10 : $i, X11 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X10 @ X11)
% 1.45/1.65           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.65  thf('129', plain,
% 1.45/1.65      ((((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 1.45/1.65          = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['127', '128'])).
% 1.45/1.65  thf('130', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.45/1.65      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.65  thf('131', plain,
% 1.45/1.65      ((((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['129', '130'])).
% 1.45/1.65  thf('132', plain,
% 1.45/1.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.45/1.65         (r1_tarski @ (k3_xboole_0 @ X14 @ X15) @ (k2_xboole_0 @ X14 @ X16))),
% 1.45/1.65      inference('cnf', [status(esa)], [t29_xboole_1])).
% 1.45/1.65  thf('133', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C))
% 1.45/1.65          | ((X0) = (k1_xboole_0))
% 1.45/1.65          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C)))),
% 1.45/1.65      inference('demod', [status(thm)], ['10', '11'])).
% 1.45/1.65  thf('134', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         (((k3_xboole_0 @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ sk_C))
% 1.45/1.65          | ((k3_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['132', '133'])).
% 1.45/1.65  thf('135', plain,
% 1.45/1.65      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['7', '12'])).
% 1.45/1.65  thf('136', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('137', plain,
% 1.45/1.65      ((((k5_xboole_0 @ sk_B @ sk_C)
% 1.45/1.65          = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['135', '136'])).
% 1.45/1.65  thf('138', plain,
% 1.45/1.65      ((((k5_xboole_0 @ sk_B @ sk_C)
% 1.45/1.65          = (k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C)))
% 1.45/1.65        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['134', '137'])).
% 1.45/1.65  thf('139', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.45/1.65      inference('sup-', [status(thm)], ['42', '43'])).
% 1.45/1.65  thf('140', plain,
% 1.45/1.65      ((((k5_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.45/1.65        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['138', '139'])).
% 1.45/1.65  thf('141', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 1.45/1.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.45/1.65  thf(t91_xboole_1, axiom,
% 1.45/1.65    (![A:$i,B:$i,C:$i]:
% 1.45/1.65     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.45/1.65       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.45/1.65  thf('142', plain,
% 1.45/1.65      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 1.45/1.65           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.45/1.65  thf('143', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.45/1.65           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['141', '142'])).
% 1.45/1.65  thf('144', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['26', '27'])).
% 1.45/1.65  thf('145', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['143', '144'])).
% 1.45/1.65  thf('146', plain,
% 1.45/1.65      ((((sk_C) = (k5_xboole_0 @ sk_B @ k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['140', '145'])).
% 1.45/1.65  thf('147', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.45/1.65      inference('cnf', [status(esa)], [t5_boole])).
% 1.45/1.65  thf('148', plain,
% 1.45/1.65      ((((sk_C) = (sk_B))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['146', '147'])).
% 1.45/1.65  thf('149', plain,
% 1.45/1.65      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['7', '12'])).
% 1.45/1.65  thf('150', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.65      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.45/1.65  thf('151', plain, ((((sk_C) != (sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup-', [status(thm)], ['149', '150'])).
% 1.45/1.65  thf('152', plain,
% 1.45/1.65      ((((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('clc', [status(thm)], ['148', '151'])).
% 1.45/1.65  thf('153', plain,
% 1.45/1.65      ((((k5_xboole_0 @ sk_B @ sk_C)
% 1.45/1.65          = (k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C)))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['135', '136'])).
% 1.45/1.65  thf('154', plain,
% 1.45/1.65      ((((k5_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_B @ k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['152', '153'])).
% 1.45/1.65  thf('155', plain,
% 1.45/1.65      ((((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((k5_xboole_0 @ sk_B @ sk_C) = (k4_xboole_0 @ sk_B @ k1_xboole_0)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['154'])).
% 1.45/1.65  thf('156', plain,
% 1.45/1.65      (![X0 : $i, X1 : $i]:
% 1.45/1.65         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['143', '144'])).
% 1.45/1.65  thf('157', plain,
% 1.45/1.65      ((((sk_C) = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ k1_xboole_0)))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['155', '156'])).
% 1.45/1.65  thf('158', plain,
% 1.45/1.65      ((((sk_C) = (k5_xboole_0 @ sk_B @ sk_B))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('sup+', [status(thm)], ['131', '157'])).
% 1.45/1.65  thf('159', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.45/1.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.45/1.65  thf('160', plain,
% 1.45/1.65      (![X10 : $i, X11 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ X10 @ X11)
% 1.45/1.65           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.45/1.65      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.45/1.65  thf('161', plain,
% 1.45/1.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['159', '160'])).
% 1.45/1.65  thf('162', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.45/1.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.45/1.65  thf('163', plain,
% 1.45/1.65      (![X8 : $i, X9 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X8 @ X9)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.45/1.65      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.45/1.65  thf('164', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k5_xboole_0 @ X0 @ X0)
% 1.45/1.65           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 1.45/1.65      inference('sup+', [status(thm)], ['162', '163'])).
% 1.45/1.65  thf('165', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 1.45/1.65      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.45/1.65  thf('166', plain,
% 1.45/1.65      (![X0 : $i]:
% 1.45/1.65         ((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['164', '165'])).
% 1.45/1.65  thf('167', plain,
% 1.45/1.65      (![X17 : $i, X18 : $i]:
% 1.45/1.65         ((k4_xboole_0 @ (k2_xboole_0 @ X17 @ X18) @ X18)
% 1.45/1.65           = (k4_xboole_0 @ X17 @ X18))),
% 1.45/1.65      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.45/1.65  thf('168', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['166', '167'])).
% 1.45/1.65  thf('169', plain,
% 1.45/1.65      ((((sk_C) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0))
% 1.45/1.65        | ((sk_B) = (k1_xboole_0)))),
% 1.45/1.65      inference('demod', [status(thm)], ['158', '161', '168'])).
% 1.45/1.65  thf('170', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['169'])).
% 1.45/1.65  thf('171', plain,
% 1.45/1.65      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.65      inference('split', [status(esa)], ['15'])).
% 1.45/1.65  thf('172', plain,
% 1.45/1.65      (((((sk_C) != (sk_C)) | ((sk_B) = (k1_xboole_0))))
% 1.45/1.65         <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.65      inference('sup-', [status(thm)], ['170', '171'])).
% 1.45/1.65  thf('173', plain,
% 1.45/1.65      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.45/1.65      inference('simplify', [status(thm)], ['172'])).
% 1.45/1.65  thf('174', plain,
% 1.45/1.65      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.65      inference('simplify', [status(thm)], ['18'])).
% 1.45/1.65  thf('175', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['113', '117'])).
% 1.45/1.65  thf('176', plain,
% 1.45/1.65      ((![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0)))
% 1.45/1.65         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.65      inference('sup+', [status(thm)], ['174', '175'])).
% 1.45/1.65  thf('177', plain, (((sk_C) != (k2_xboole_0 @ sk_B @ sk_C))),
% 1.45/1.65      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 1.45/1.65  thf('178', plain,
% 1.45/1.65      ((((sk_C) != (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.45/1.65      inference('sup-', [status(thm)], ['176', '177'])).
% 1.45/1.65  thf('179', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.45/1.65      inference('simplify', [status(thm)], ['178'])).
% 1.45/1.65  thf('180', plain,
% 1.45/1.65      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.45/1.65      inference('split', [status(esa)], ['15'])).
% 1.45/1.65  thf('181', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 1.45/1.65      inference('sat_resolution*', [status(thm)], ['179', '180'])).
% 1.45/1.65  thf('182', plain, (((sk_B) = (k1_xboole_0))),
% 1.45/1.65      inference('simpl_trail', [status(thm)], ['173', '181'])).
% 1.45/1.65  thf('183', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B @ X0))),
% 1.45/1.65      inference('demod', [status(thm)], ['118', '182'])).
% 1.45/1.65  thf('184', plain, (((sk_C) != (sk_C))),
% 1.45/1.65      inference('demod', [status(thm)], ['24', '183'])).
% 1.45/1.65  thf('185', plain, ($false), inference('simplify', [status(thm)], ['184'])).
% 1.45/1.65  
% 1.45/1.65  % SZS output end Refutation
% 1.45/1.65  
% 1.45/1.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
