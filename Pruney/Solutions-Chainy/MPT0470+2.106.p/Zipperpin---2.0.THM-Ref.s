%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ViViVsir5h

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:42 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 157 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  652 (1040 expanded)
%              Number of equality atoms :   56 ( 115 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('30',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ ( k2_relat_1 @ X0 ) )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k2_relat_1 @ X1 ) ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k2_relat_1 @ X1 ) ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ ( k2_relat_1 @ X1 ) ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','8'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('68',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['38','68'])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ViViVsir5h
% 0.15/0.38  % Computer   : n013.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:21:55 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 205 iterations in 0.125s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.62  thf(dt_k5_relat_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.38/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X15)
% 0.38/0.62          | ~ (v1_relat_1 @ X16)
% 0.38/0.62          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.62  thf(t60_relat_1, axiom,
% 0.38/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.62  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.62  thf(t45_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( v1_relat_1 @ B ) =>
% 0.38/0.62           ( r1_tarski @
% 0.38/0.62             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X21)
% 0.38/0.62          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 0.38/0.62             (k2_relat_1 @ X21))
% 0.38/0.62          | ~ (v1_relat_1 @ X22))),
% 0.38/0.62      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.38/0.62           k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf(d1_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) <=>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.62              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X12 : $i]: ((v1_relat_1 @ X12) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.38/0.62      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.38/0.62  thf(t113_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X6 : $i, X7 : $i]:
% 0.38/0.62         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.38/0.62  thf(t152_zfmisc_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.38/0.62      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.38/0.62  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.62  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.38/0.62           k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['3', '9'])).
% 0.38/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.62  thf('11', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.38/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.62  thf(d10_xboole_0, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      (![X1 : $i, X3 : $i]:
% 0.38/0.62         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.38/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.62  thf(fc9_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.38/0.62       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (![X18 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (k2_relat_1 @ X18))
% 0.38/0.62          | ~ (v1_relat_1 @ X18)
% 0.38/0.62          | (v1_xboole_0 @ X18))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.62  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '18'])).
% 0.38/0.62  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '8'])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['21'])).
% 0.38/0.62  thf(l13_xboole_0, axiom,
% 0.38/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('24', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.62  thf('25', plain,
% 0.38/0.62      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf('26', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('27', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('28', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.62  thf('29', plain,
% 0.38/0.62      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['23', '24'])).
% 0.38/0.62  thf(t62_relat_1, conjecture,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.38/0.62         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i]:
% 0.38/0.62        ( ( v1_relat_1 @ A ) =>
% 0.38/0.62          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.38/0.62            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.38/0.62        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('31', plain,
% 0.38/0.62      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('split', [status(esa)], ['30'])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (((k5_relat_1 @ sk_A @ (k2_relat_1 @ X0)) != (k1_xboole_0))
% 0.38/0.62           | ~ (v1_xboole_0 @ X0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['29', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      ((![X0 : $i, X1 : $i]:
% 0.38/0.62          (((X0) != (k1_xboole_0))
% 0.38/0.62           | ~ (v1_xboole_0 @ X0)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k2_relat_1 @ X1)))
% 0.38/0.62           | ~ (v1_xboole_0 @ X1)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['28', '32'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      ((![X1 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ X1)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k2_relat_1 @ X1)))
% 0.38/0.62           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.62  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      ((![X1 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ X1)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ (k2_relat_1 @ X1)))))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('simplify_reflect+', [status(thm)], ['34', '35'])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.38/0.62           | ~ (v1_xboole_0 @ X0)
% 0.38/0.62           | ~ (v1_xboole_0 @ X0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['25', '36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ X0)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.38/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['37'])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      (![X15 : $i, X16 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X15)
% 0.38/0.62          | ~ (v1_relat_1 @ X16)
% 0.38/0.62          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.38/0.62  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.62  thf(t44_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( v1_relat_1 @ A ) =>
% 0.38/0.62       ( ![B:$i]:
% 0.38/0.62         ( ( v1_relat_1 @ B ) =>
% 0.38/0.62           ( r1_tarski @
% 0.38/0.62             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X19)
% 0.38/0.62          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.38/0.62             (k1_relat_1 @ X20))
% 0.38/0.62          | ~ (v1_relat_1 @ X20))),
% 0.38/0.62      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.38/0.62           k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.38/0.62  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '8'])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.38/0.62           k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.62  thf(fc8_relat_1, axiom,
% 0.38/0.62    (![A:$i]:
% 0.38/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.38/0.62       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.38/0.62  thf('47', plain,
% 0.38/0.62      (![X17 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ (k1_relat_1 @ X17))
% 0.38/0.62          | ~ (v1_relat_1 @ X17)
% 0.38/0.62          | (v1_xboole_0 @ X17))),
% 0.38/0.62      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.38/0.62          | ~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.62  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['48', '49'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['39', '50'])).
% 0.38/0.62  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['4', '8'])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_relat_1 @ X0)
% 0.38/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.38/0.62          | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.38/0.62      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.62  thf('55', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.38/0.62  thf('56', plain,
% 0.38/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.38/0.62  thf('57', plain,
% 0.38/0.62      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('split', [status(esa)], ['30'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      ((![X0 : $i]:
% 0.38/0.62          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.62  thf('59', plain,
% 0.38/0.62      ((![X0 : $i, X1 : $i]:
% 0.38/0.62          (((X0) != (k1_xboole_0))
% 0.38/0.62           | ~ (v1_xboole_0 @ X0)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.38/0.62           | ~ (v1_xboole_0 @ X1)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['55', '58'])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      ((![X1 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ X1)
% 0.38/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.38/0.62           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['59'])).
% 0.38/0.62  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      ((![X1 : $i]:
% 0.38/0.62          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.38/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['54', '62'])).
% 0.38/0.62  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.62  thf('66', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.38/0.62       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.38/0.62      inference('split', [status(esa)], ['30'])).
% 0.38/0.62  thf('68', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.38/0.62      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (v1_xboole_0 @ X0)
% 0.38/0.62          | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))),
% 0.38/0.62      inference('simpl_trail', [status(thm)], ['38', '68'])).
% 0.38/0.62  thf('70', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))),
% 0.38/0.62      inference('condensation', [status(thm)], ['69'])).
% 0.38/0.62  thf('71', plain, (~ (v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('sup-', [status(thm)], ['22', '70'])).
% 0.38/0.62  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('73', plain, ($false), inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
