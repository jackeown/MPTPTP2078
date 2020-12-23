%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wSrh99WtE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:44 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 133 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  550 ( 881 expanded)
%              Number of equality atoms :   52 ( 102 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','10','11'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

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

thf('23',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('26',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('31',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('56',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['24','56'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9wSrh99WtE
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:37:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 169 iterations in 0.148s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.43/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.43/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.62  thf(dt_k5_relat_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.43/0.62       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X12)
% 0.43/0.62          | ~ (v1_relat_1 @ X13)
% 0.43/0.62          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.62  thf(t60_relat_1, axiom,
% 0.43/0.62    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.43/0.62     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.43/0.62  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.43/0.62  thf(t47_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( v1_relat_1 @ B ) =>
% 0.43/0.62           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.43/0.62             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (![X18 : $i, X19 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X18)
% 0.43/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ X19)) = (k2_relat_1 @ X19))
% 0.43/0.62          | ~ (r1_tarski @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X18))
% 0.43/0.62          | ~ (v1_relat_1 @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.62          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.62              = (k2_relat_1 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.62  thf('4', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.62  thf(d1_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) <=>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ~( ( r2_hidden @ B @ A ) & 
% 0.43/0.62              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (![X9 : $i]: ((v1_relat_1 @ X9) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.43/0.62  thf(t113_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i]:
% 0.43/0.62         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['6'])).
% 0.43/0.62  thf(t152_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.43/0.62      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.43/0.62  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.62  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '9'])).
% 0.43/0.62  thf('11', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['3', '4', '10', '11'])).
% 0.43/0.62  thf(fc9_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.43/0.62       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X15 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 0.43/0.62          | ~ (v1_relat_1 @ X15)
% 0.43/0.62          | (v1_xboole_0 @ X15))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.62  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.62  thf('16', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '16'])).
% 0.43/0.62  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '9'])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['19'])).
% 0.43/0.62  thf(l13_xboole_0, axiom,
% 0.43/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf(t62_relat_1, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.43/0.62         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( v1_relat_1 @ A ) =>
% 0.43/0.62          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.43/0.62            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.43/0.62        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (![X12 : $i, X13 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X12)
% 0.43/0.62          | ~ (v1_relat_1 @ X13)
% 0.43/0.62          | (v1_relat_1 @ (k5_relat_1 @ X12 @ X13)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.43/0.62  thf('26', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.43/0.62  thf(t46_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_relat_1 @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( v1_relat_1 @ B ) =>
% 0.43/0.62           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.43/0.62             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (![X16 : $i, X17 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X16)
% 0.43/0.62          | ((k1_relat_1 @ (k5_relat_1 @ X17 @ X16)) = (k1_relat_1 @ X17))
% 0.43/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ (k1_relat_1 @ X16))
% 0.43/0.62          | ~ (v1_relat_1 @ X17))),
% 0.43/0.62      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.62          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.62              = (k1_relat_1 @ k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.43/0.62  thf('29', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.43/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.62  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '9'])).
% 0.43/0.62  thf('31', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.43/0.62  thf(fc8_relat_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.43/0.62       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X14 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ (k1_relat_1 @ X14))
% 0.43/0.62          | ~ (v1_relat_1 @ X14)
% 0.43/0.62          | (v1_xboole_0 @ X14))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.43/0.62          | ~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '36'])).
% 0.43/0.62  thf('38', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '9'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v1_relat_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.43/0.62          | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.62      inference('sup+', [status(thm)], ['41', '42'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('split', [status(esa)], ['23'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i]:
% 0.43/0.62          (((X0) != (k1_xboole_0))
% 0.43/0.62           | ~ (v1_xboole_0 @ X0)
% 0.43/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.43/0.62           | ~ (v1_xboole_0 @ X1)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      ((![X1 : $i]:
% 0.43/0.62          (~ (v1_xboole_0 @ X1)
% 0.43/0.62           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.43/0.62           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['47'])).
% 0.43/0.62  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      ((![X1 : $i]:
% 0.43/0.62          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('simplify_reflect+', [status(thm)], ['48', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.43/0.62         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['40', '50'])).
% 0.43/0.62  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.62  thf('54', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.43/0.62  thf('55', plain,
% 0.43/0.62      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.43/0.62       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.43/0.62      inference('split', [status(esa)], ['23'])).
% 0.43/0.62  thf('56', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.43/0.62  thf('57', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['24', '56'])).
% 0.43/0.62  thf('58', plain,
% 0.43/0.62      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['22', '57'])).
% 0.43/0.62  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('60', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.43/0.62      inference('demod', [status(thm)], ['58', '59'])).
% 0.43/0.62  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.43/0.62  
% 0.43/0.62  % SZS output end Refutation
% 0.43/0.62  
% 0.43/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
