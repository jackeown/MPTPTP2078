%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bESdneye9l

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:44 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  184 (2833 expanded)
%              Number of leaves         :   35 ( 884 expanded)
%              Depth                    :   37
%              Number of atoms          : 1665 (28054 expanded)
%              Number of equality atoms :  230 (3512 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t58_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
        = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A )
          = ( k4_zfmisc_1 @ B @ B @ B @ B ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_mcart_1])).

thf('0',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X15: $i] :
      ( ( k2_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k5_xboole_0 @ X11 @ X12 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X11 @ X12 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','23'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('25',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) )
      | ~ ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t53_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ) )).

thf('29',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ k1_xboole_0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('32',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X28 @ X29 ) @ ( k2_zfmisc_1 @ X30 @ X31 ) )
      | ~ ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X22 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X3 ) ) ),
    inference(demod,[status(thm)],['30','35','36'])).

thf('38',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D )
      = ( k4_zfmisc_1 @ A @ B @ C @ D ) ) )).

thf('39',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) @ X56 @ X57 )
      = ( k4_zfmisc_1 @ X54 @ X55 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t54_mcart_1])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_xboole_0 @ k1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r2_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('50',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('51',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t138_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf('52',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r1_tarski @ X0 @ X4 )
      | ( ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) )
      | ( r1_tarski @ X0 @ X4 )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) )
      | ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t60_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r2_xboole_0 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t60_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('73',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('74',plain,
    ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
    = ( k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('76',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_zfmisc_1 @ X34 @ X35 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X37 ) )
      | ( r1_tarski @ X35 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t138_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X4 ) @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ X4 @ X0 )
      | ( ( k2_zfmisc_1 @ X5 @ X4 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) @ ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['72','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X3 @ X2 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('84',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ X0 ) )
      | ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = sk_B )
      | ( r2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X42 @ X43 @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t130_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) )
         != k1_xboole_0 ) ) ) )).

thf('97',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X32 @ ( k1_tarski @ X33 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t130_zfmisc_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_xboole_0 @ sk_A @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X1 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_xboole_0 @ sk_A @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( r2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['71','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('107',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( ( k3_zfmisc_1 @ sk_A @ sk_A @ X1 )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('113',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('114',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('115',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['45','112','113','114'])).

thf('116',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_zfmisc_1 @ sk_B @ sk_B )
      = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 != X4 )
      | ~ ( r2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('119',plain,(
    ! [X4: $i] :
      ~ ( r2_xboole_0 @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( k2_zfmisc_1 @ sk_B @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['117','119'])).

thf('121',plain,(
    ! [X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ( k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t53_mcart_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('124',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('125',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0 )
      = ( k2_zfmisc_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['122','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0 )
      = sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ ( k1_tarski @ X0 ) )
       != k1_xboole_0 )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('131',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('132',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ ( k1_tarski @ X0 ) )
       != sk_A )
      | ( ( k3_zfmisc_1 @ X3 @ X2 @ X1 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X1: $i] :
      ( ( sk_A != sk_A )
      | ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['129','133'])).

thf('135',plain,(
    ! [X1: $i] :
      ( ( k3_zfmisc_1 @ sk_B @ sk_B @ X1 )
      = sk_A ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
       != k1_xboole_0 )
      | ( X48 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('137',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('138',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('139',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('140',plain,(
    sk_A = k1_xboole_0 ),
    inference(condensation,[status(thm)],['111'])).

thf('141',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k3_zfmisc_1 @ X46 @ X47 @ X48 )
       != sk_A )
      | ( X48 = sk_A )
      | ( X47 = sk_A )
      | ( X46 = sk_A ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( sk_A != sk_A )
      | ( sk_B = sk_A )
      | ( sk_B = sk_A )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['135','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( sk_B = sk_A ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X0: $i] : ( X0 = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['143','144'])).

thf('146',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','145'])).

thf('147',plain,(
    $false ),
    inference(simplify,[status(thm)],['146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bESdneye9l
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 894 iterations in 0.350s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.59/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.59/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.81  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(t58_mcart_1, conjecture,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.59/0.81       ( ( A ) = ( B ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i,B:$i]:
% 0.59/0.81        ( ( ( k4_zfmisc_1 @ A @ A @ A @ A ) = ( k4_zfmisc_1 @ B @ B @ B @ B ) ) =>
% 0.59/0.81          ( ( A ) = ( B ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t58_mcart_1])).
% 0.59/0.81  thf('0', plain, (((sk_A) != (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(idempotence_k3_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.81  thf('1', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.81  thf(t4_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.81            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.81       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.81            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         ((r1_xboole_0 @ X7 @ X8)
% 0.59/0.81          | (r2_hidden @ (sk_C @ X8 @ X7) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((r2_hidden @ (sk_C @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.81  thf(t1_boole, axiom,
% 0.59/0.81    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.81  thf('4', plain, (![X15 : $i]: ((k2_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.59/0.81      inference('cnf', [status(esa)], [t1_boole])).
% 0.59/0.81  thf(l98_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( k5_xboole_0 @ A @ B ) =
% 0.59/0.81       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.81  thf('5', plain,
% 0.59/0.81      (![X11 : $i, X12 : $i]:
% 0.59/0.81         ((k5_xboole_0 @ X11 @ X12)
% 0.59/0.81           = (k4_xboole_0 @ (k2_xboole_0 @ X11 @ X12) @ 
% 0.59/0.81              (k3_xboole_0 @ X11 @ X12)))),
% 0.59/0.81      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.59/0.81           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['4', '5'])).
% 0.59/0.81  thf(t5_boole, axiom,
% 0.59/0.81    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.81  thf('7', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((X0) = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.81  thf(t38_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.59/0.81       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('9', plain,
% 0.59/0.81      (![X16 : $i, X17 : $i]:
% 0.59/0.81         (((X16) = (k1_xboole_0))
% 0.59/0.81          | ~ (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.59/0.81          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.81  thf(t17_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.59/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.59/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.81  thf(d8_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.59/0.81       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (![X3 : $i, X5 : $i]:
% 0.59/0.81         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k3_xboole_0 @ X0 @ X1) = (X0))
% 0.59/0.81          | (r2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         ((r2_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (X0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['12', '15'])).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.59/0.81          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.59/0.81      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.81  thf('18', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X1 @ X0)
% 0.59/0.81          | (r2_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.81          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.81      inference('demod', [status(thm)], ['10', '11'])).
% 0.59/0.81  thf(d7_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.81       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (![X0 : $i, X2 : $i]:
% 0.59/0.81         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.81  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.81      inference('simplify', [status(thm)], ['21'])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (r2_hidden @ X1 @ X0) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['18', '22'])).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (![X0 : $i]: ((r1_xboole_0 @ X0 @ X0) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['3', '23'])).
% 0.59/0.81  thf(t127_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.59/0.81       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.81         ((r1_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ (k2_zfmisc_1 @ X30 @ X31))
% 0.59/0.81          | ~ (r1_xboole_0 @ X28 @ X30))),
% 0.59/0.81      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((r2_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.81          | (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.81  thf(t66_xboole_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.59/0.81       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.59/0.81      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((r2_xboole_0 @ k1_xboole_0 @ X1)
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.81  thf(t53_mcart_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.59/0.81       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) @ D ) ))).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0))
% 0.59/0.81          | (r2_xboole_0 @ k1_xboole_0 @ X3))),
% 0.59/0.81      inference('sup+', [status(thm)], ['28', '29'])).
% 0.59/0.81  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.81      inference('simplify', [status(thm)], ['21'])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.81         ((r1_xboole_0 @ (k2_zfmisc_1 @ X28 @ X29) @ (k2_zfmisc_1 @ X30 @ X31))
% 0.59/0.81          | ~ (r1_xboole_0 @ X28 @ X30))),
% 0.59/0.81      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X2) @ 
% 0.59/0.81          (k2_zfmisc_1 @ k1_xboole_0 @ X1))),
% 0.59/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      (![X22 : $i]: (((X22) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X22 @ X22))),
% 0.59/0.81      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('36', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ k1_xboole_0 @ X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['30', '35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t54_mcart_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C @ D ) =
% 0.59/0.81       ( k4_zfmisc_1 @ A @ B @ C @ D ) ))).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 0.59/0.81         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55) @ X56 @ X57)
% 0.59/0.81           = (k4_zfmisc_1 @ X54 @ X55 @ X56 @ X57))),
% 0.59/0.81      inference('cnf', [status(esa)], [t54_mcart_1])).
% 0.59/0.81  thf(t35_mcart_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.81         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.59/0.81       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.59/0.81          | ((X48) = (k1_xboole_0))
% 0.59/0.81          | ((X47) = (k1_xboole_0))
% 0.59/0.81          | ((X46) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['38', '41'])).
% 0.59/0.81  thf('43', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) != (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['42'])).
% 0.59/0.81  thf('44', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | (r2_xboole_0 @ k1_xboole_0 @ sk_A)
% 0.59/0.81        | ((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['37', '43'])).
% 0.59/0.81  thf('45', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0))
% 0.59/0.81        | (r2_xboole_0 @ k1_xboole_0 @ sk_A))),
% 0.59/0.81      inference('simplify', [status(thm)], ['44'])).
% 0.59/0.81  thf('46', plain, (![X6 : $i]: ((k3_xboole_0 @ X6 @ X6) = (X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (![X13 : $i, X14 : $i]: (r1_tarski @ (k3_xboole_0 @ X13 @ X14) @ X13)),
% 0.59/0.81      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.59/0.81  thf('48', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.81      inference('sup+', [status(thm)], ['46', '47'])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(d4_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.59/0.81       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X42 @ X43 @ X44) @ X45))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf(t138_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.59/0.81       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.81         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.59/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.59/0.81               (k2_zfmisc_1 @ X36 @ X37))
% 0.59/0.81          | (r1_tarski @ X35 @ X37))),
% 0.59/0.81      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.59/0.81  thf('53', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.81             (k2_zfmisc_1 @ X5 @ X4))
% 0.59/0.81          | (r1_tarski @ X0 @ X4)
% 0.59/0.81          | ((k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.81  thf('54', plain,
% 0.59/0.81      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X42 @ X43 @ X44) @ X45))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('55', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.81             (k2_zfmisc_1 @ X5 @ X4))
% 0.59/0.81          | (r1_tarski @ X0 @ X4)
% 0.59/0.81          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['53', '54'])).
% 0.59/0.81  thf('56', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.59/0.81             (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B) = (k1_xboole_0))
% 0.59/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['50', '55'])).
% 0.59/0.81  thf('57', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('58', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.59/0.81             (k2_zfmisc_1 @ X1 @ X0))
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.81          | (r1_tarski @ sk_B @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['56', '57'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) @ 
% 0.59/0.81             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81          | (r1_tarski @ sk_B @ X0)
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['49', '58'])).
% 0.59/0.81  thf('60', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_B @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['48', '59'])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_B @ sk_A)
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_B @ sk_A))),
% 0.59/0.81      inference('simplify', [status(thm)], ['62'])).
% 0.59/0.81  thf('64', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('65', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0))
% 0.59/0.81          | (r1_tarski @ sk_B @ sk_A)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['63', '64'])).
% 0.59/0.81  thf('66', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('67', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.59/0.81          | (r1_tarski @ sk_B @ sk_A)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.59/0.81  thf('68', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | (r1_tarski @ sk_B @ sk_A)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['67', '68'])).
% 0.59/0.81  thf(t60_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]: ( ~( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ A ) ) ))).
% 0.59/0.81  thf('70', plain,
% 0.59/0.81      (![X19 : $i, X20 : $i]:
% 0.59/0.81         (~ (r1_tarski @ X19 @ X20) | ~ (r2_xboole_0 @ X20 @ X19))),
% 0.59/0.81      inference('cnf', [status(esa)], [t60_xboole_1])).
% 0.59/0.81  thf('71', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | ~ (r2_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.81  thf('72', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.59/0.81      inference('sup+', [status(thm)], ['46', '47'])).
% 0.59/0.81  thf('73', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('74', plain,
% 0.59/0.81      (((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A)
% 0.59/0.81         = (k4_zfmisc_1 @ sk_B @ sk_B @ sk_B @ sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('75', plain,
% 0.59/0.81      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X42 @ X43 @ X44) @ X45))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf('76', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.81         (((k2_zfmisc_1 @ X34 @ X35) = (k1_xboole_0))
% 0.59/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 0.59/0.81               (k2_zfmisc_1 @ X36 @ X37))
% 0.59/0.81          | (r1_tarski @ X35 @ X37))),
% 0.59/0.81      inference('cnf', [status(esa)], [t138_zfmisc_1])).
% 0.59/0.81  thf('77', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X5 @ X4) @ 
% 0.59/0.81             (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.59/0.81          | (r1_tarski @ X4 @ X0)
% 0.59/0.81          | ((k2_zfmisc_1 @ X5 @ X4) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.81  thf('78', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.59/0.81             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.59/0.81          | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | (r1_tarski @ X0 @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['74', '77'])).
% 0.59/0.81  thf('79', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.81             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.59/0.81          | (r1_tarski @ X0 @ sk_B)
% 0.59/0.81          | ((k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1) @ X0)
% 0.59/0.81              = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['73', '78'])).
% 0.59/0.81  thf('80', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('81', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) @ 
% 0.59/0.81             (k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A))
% 0.59/0.81          | (r1_tarski @ X0 @ sk_B)
% 0.59/0.81          | ((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['79', '80'])).
% 0.59/0.81  thf('82', plain,
% 0.59/0.81      ((((k4_zfmisc_1 @ sk_A @ sk_A @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_A @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['72', '81'])).
% 0.59/0.81  thf('83', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X3 @ X2) = (k1_xboole_0))
% 0.59/0.81          | ((X1) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('84', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_A @ sk_B)
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.81  thf('85', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k1_xboole_0))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0))
% 0.59/0.81        | (r1_tarski @ sk_A @ sk_B))),
% 0.59/0.81      inference('simplify', [status(thm)], ['84'])).
% 0.59/0.81  thf('86', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('87', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ X0))
% 0.59/0.81          | (r1_tarski @ sk_A @ sk_B)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['85', '86'])).
% 0.59/0.81  thf('88', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('89', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0)
% 0.59/0.81            = (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.59/0.81          | (r1_tarski @ sk_A @ sk_B)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['87', '88'])).
% 0.59/0.81  thf('90', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('91', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | (r1_tarski @ sk_A @ sk_B)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['89', '90'])).
% 0.59/0.81  thf('92', plain,
% 0.59/0.81      (![X3 : $i, X5 : $i]:
% 0.59/0.81         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.81  thf('93', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (sk_B))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['91', '92'])).
% 0.59/0.81  thf('94', plain, (((sk_A) != (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('95', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.59/0.81  thf('96', plain,
% 0.59/0.81      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X42 @ X43 @ X44 @ X45)
% 0.59/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X42 @ X43 @ X44) @ X45))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.59/0.81  thf(t130_zfmisc_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.59/0.81       ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ A ) != ( k1_xboole_0 ) ) & 
% 0.59/0.81         ( ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.59/0.81  thf('97', plain,
% 0.59/0.81      (![X32 : $i, X33 : $i]:
% 0.59/0.81         (((X32) = (k1_xboole_0))
% 0.59/0.81          | ((k2_zfmisc_1 @ X32 @ (k1_tarski @ X33)) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t130_zfmisc_1])).
% 0.59/0.81  thf('98', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['96', '97'])).
% 0.59/0.81  thf('99', plain,
% 0.59/0.81      (![X1 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ sk_A @ sk_A @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['95', '98'])).
% 0.59/0.81  thf('100', plain,
% 0.59/0.81      (![X1 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_A @ sk_A @ X1) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('simplify', [status(thm)], ['99'])).
% 0.59/0.81  thf('101', plain,
% 0.59/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.59/0.81          | ((X48) = (k1_xboole_0))
% 0.59/0.81          | ((X47) = (k1_xboole_0))
% 0.59/0.81          | ((X46) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('102', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B)
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['100', '101'])).
% 0.59/0.81  thf('103', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.81      inference('simplify', [status(thm)], ['102'])).
% 0.59/0.81  thf('104', plain, (((r2_xboole_0 @ sk_A @ sk_B) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('condensation', [status(thm)], ['103'])).
% 0.59/0.81  thf('105', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ sk_A @ sk_A @ X1 @ X0) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('clc', [status(thm)], ['71', '104'])).
% 0.59/0.81  thf('106', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['96', '97'])).
% 0.59/0.81  thf('107', plain,
% 0.59/0.81      (![X1 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ sk_A @ sk_A @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['105', '106'])).
% 0.59/0.81  thf('108', plain,
% 0.59/0.81      (![X1 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ sk_A @ sk_A @ X1) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['107'])).
% 0.59/0.81  thf('109', plain,
% 0.59/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.59/0.81          | ((X48) = (k1_xboole_0))
% 0.59/0.81          | ((X47) = (k1_xboole_0))
% 0.59/0.81          | ((X46) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('110', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((sk_A) = (k1_xboole_0))
% 0.59/0.81          | ((X0) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['108', '109'])).
% 0.59/0.81  thf('111', plain,
% 0.59/0.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['110'])).
% 0.59/0.81  thf('112', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('113', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('114', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('115', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))
% 0.59/0.81        | ((sk_B) = (sk_A))
% 0.59/0.81        | (r2_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['45', '112', '113', '114'])).
% 0.59/0.81  thf('116', plain, (((sk_A) != (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('117', plain,
% 0.59/0.81      ((((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A)) | (r2_xboole_0 @ sk_A @ sk_A))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['115', '116'])).
% 0.59/0.81  thf('118', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i]: (((X3) != (X4)) | ~ (r2_xboole_0 @ X3 @ X4))),
% 0.59/0.81      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.59/0.81  thf('119', plain, (![X4 : $i]: ~ (r2_xboole_0 @ X4 @ X4)),
% 0.59/0.81      inference('simplify', [status(thm)], ['118'])).
% 0.59/0.81  thf('120', plain, (((k2_zfmisc_1 @ sk_B @ sk_B) = (sk_A))),
% 0.59/0.81      inference('clc', [status(thm)], ['117', '119'])).
% 0.59/0.81  thf('121', plain,
% 0.59/0.81      (![X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ X50 @ X51 @ X52 @ X53)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51) @ X52) @ 
% 0.59/0.81              X53))),
% 0.59/0.81      inference('cnf', [status(esa)], [t53_mcart_1])).
% 0.59/0.81  thf('122', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0)
% 0.59/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1) @ X0))),
% 0.59/0.81      inference('sup+', [status(thm)], ['120', '121'])).
% 0.59/0.81  thf('123', plain,
% 0.59/0.81      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.81  thf('124', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('125', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('126', plain, (![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.59/0.81  thf('127', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         ((k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0) = (k2_zfmisc_1 @ sk_A @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['122', '126'])).
% 0.59/0.81  thf('128', plain, (![X0 : $i]: ((k2_zfmisc_1 @ sk_A @ X0) = (sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.59/0.81  thf('129', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((k4_zfmisc_1 @ sk_B @ sk_B @ X1 @ X0) = (sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['127', '128'])).
% 0.59/0.81  thf('130', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))
% 0.59/0.81          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['96', '97'])).
% 0.59/0.81  thf('131', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('132', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('133', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.81         (((k4_zfmisc_1 @ X3 @ X2 @ X1 @ (k1_tarski @ X0)) != (sk_A))
% 0.59/0.81          | ((k3_zfmisc_1 @ X3 @ X2 @ X1) = (sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.59/0.81  thf('134', plain,
% 0.59/0.81      (![X1 : $i]:
% 0.59/0.81         (((sk_A) != (sk_A)) | ((k3_zfmisc_1 @ sk_B @ sk_B @ X1) = (sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['129', '133'])).
% 0.59/0.81  thf('135', plain, (![X1 : $i]: ((k3_zfmisc_1 @ sk_B @ sk_B @ X1) = (sk_A))),
% 0.59/0.81      inference('simplify', [status(thm)], ['134'])).
% 0.59/0.81  thf('136', plain,
% 0.59/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X46 @ X47 @ X48) != (k1_xboole_0))
% 0.59/0.81          | ((X48) = (k1_xboole_0))
% 0.59/0.81          | ((X47) = (k1_xboole_0))
% 0.59/0.81          | ((X46) = (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.81  thf('137', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('138', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('139', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('140', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.81      inference('condensation', [status(thm)], ['111'])).
% 0.59/0.81  thf('141', plain,
% 0.59/0.81      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.81         (((k3_zfmisc_1 @ X46 @ X47 @ X48) != (sk_A))
% 0.59/0.81          | ((X48) = (sk_A))
% 0.59/0.81          | ((X47) = (sk_A))
% 0.59/0.81          | ((X46) = (sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 0.59/0.81  thf('142', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (((sk_A) != (sk_A))
% 0.59/0.81          | ((sk_B) = (sk_A))
% 0.59/0.81          | ((sk_B) = (sk_A))
% 0.59/0.81          | ((X0) = (sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['135', '141'])).
% 0.59/0.81  thf('143', plain, (![X0 : $i]: (((X0) = (sk_A)) | ((sk_B) = (sk_A)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['142'])).
% 0.59/0.81  thf('144', plain, (((sk_A) != (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('145', plain, (![X0 : $i]: ((X0) = (sk_A))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['143', '144'])).
% 0.59/0.81  thf('146', plain, (((sk_A) != (sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '145'])).
% 0.59/0.81  thf('147', plain, ($false), inference('simplify', [status(thm)], ['146'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
