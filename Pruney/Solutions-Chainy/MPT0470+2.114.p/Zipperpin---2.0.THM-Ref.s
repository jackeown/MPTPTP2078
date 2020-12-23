%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sKICK7m7S

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:43 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 205 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :   17
%              Number of atoms          :  747 (1392 expanded)
%              Number of equality atoms :   61 ( 122 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X26 @ X25 ) ) @ ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ X18 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('11',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ X18 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ~ ( r2_hidden @ X14 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['19','27'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','32'])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','15'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

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

thf('41',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('51',plain,
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

thf('52',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','15'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','61'])).

thf('63',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','15'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['41'])).

thf('79',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['49','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['81','82','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sKICK7m7S
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:51:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.47/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.65  % Solved by: fo/fo7.sh
% 0.47/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.65  % done 341 iterations in 0.190s
% 0.47/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.65  % SZS output start Refutation
% 0.47/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.65  thf(dt_k5_relat_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.47/0.65       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.47/0.65  thf('0', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X21)
% 0.47/0.65          | ~ (v1_relat_1 @ X22)
% 0.47/0.65          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.65  thf(t60_relat_1, axiom,
% 0.47/0.65    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.65  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf(t45_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( v1_relat_1 @ B ) =>
% 0.47/0.65           ( r1_tarski @
% 0.47/0.65             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.47/0.65  thf('2', plain,
% 0.47/0.65      (![X25 : $i, X26 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X25)
% 0.47/0.65          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X26 @ X25)) @ 
% 0.47/0.65             (k2_relat_1 @ X25))
% 0.47/0.65          | ~ (v1_relat_1 @ X26))),
% 0.47/0.65      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.47/0.65  thf('3', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.65           k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.47/0.65      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.65  thf('4', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.65  thf(t28_xboole_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.47/0.65  thf('5', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.65  thf('6', plain,
% 0.47/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.65  thf(d7_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.65  thf('7', plain,
% 0.47/0.65      (![X0 : $i, X2 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.65  thf('8', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.65  thf('9', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.47/0.65      inference('simplify', [status(thm)], ['8'])).
% 0.47/0.65  thf(d1_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) <=>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ~( ( r2_hidden @ B @ A ) & 
% 0.47/0.65              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.47/0.65  thf('10', plain,
% 0.47/0.65      (![X18 : $i]: ((v1_relat_1 @ X18) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.47/0.65  thf('11', plain,
% 0.47/0.65      (![X18 : $i]: ((v1_relat_1 @ X18) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.47/0.65      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.47/0.65  thf(t3_xboole_0, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.47/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.47/0.65  thf('12', plain,
% 0.47/0.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.47/0.65         (~ (r2_hidden @ X6 @ X4)
% 0.47/0.65          | ~ (r2_hidden @ X6 @ X7)
% 0.47/0.65          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.65  thf('13', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         ((v1_relat_1 @ X0)
% 0.47/0.65          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.47/0.65          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.47/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.65  thf('14', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_relat_1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['10', '13'])).
% 0.47/0.65  thf('15', plain,
% 0.47/0.65      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.65  thf('16', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.47/0.65  thf('17', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.65           k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['3', '16'])).
% 0.47/0.65  thf('18', plain,
% 0.47/0.65      (![X8 : $i, X9 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.47/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.47/0.65  thf('19', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.47/0.65              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.47/0.65  thf('20', plain,
% 0.47/0.65      (![X4 : $i, X5 : $i]:
% 0.47/0.65         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 0.47/0.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.47/0.65  thf(t113_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]:
% 0.47/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.47/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.65  thf('21', plain,
% 0.47/0.65      (![X12 : $i, X13 : $i]:
% 0.47/0.65         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.47/0.65          | ((X13) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.47/0.65  thf('22', plain,
% 0.47/0.65      (![X12 : $i]: ((k2_zfmisc_1 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.65  thf(t152_zfmisc_1, axiom,
% 0.47/0.65    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.47/0.65  thf('23', plain,
% 0.47/0.65      (![X14 : $i, X15 : $i]: ~ (r2_hidden @ X14 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.47/0.65      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.47/0.65  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.65  thf('25', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['20', '24'])).
% 0.47/0.65  thf('26', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.47/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.65  thf('27', plain,
% 0.47/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.65  thf('28', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.47/0.65      inference('demod', [status(thm)], ['19', '27'])).
% 0.47/0.65  thf(fc9_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('29', plain,
% 0.47/0.65      (![X24 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (k2_relat_1 @ X24))
% 0.47/0.65          | ~ (v1_relat_1 @ X24)
% 0.47/0.65          | (v1_xboole_0 @ X24))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.47/0.65  thf('30', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.65  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('32', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.65  thf('33', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['0', '32'])).
% 0.47/0.65  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.47/0.65  thf('35', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.47/0.65  thf('36', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['35'])).
% 0.47/0.65  thf(l13_xboole_0, axiom,
% 0.47/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.65  thf('37', plain,
% 0.47/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('38', plain,
% 0.47/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('39', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.65  thf('40', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.65  thf(t62_relat_1, conjecture,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.65    (~( ![A:$i]:
% 0.47/0.65        ( ( v1_relat_1 @ A ) =>
% 0.47/0.65          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.47/0.65            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.47/0.65    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.47/0.65  thf('41', plain,
% 0.47/0.65      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.47/0.65        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('42', plain,
% 0.47/0.65      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('split', [status(esa)], ['41'])).
% 0.47/0.65  thf('43', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (((X0) != (k1_xboole_0))
% 0.47/0.65           | ~ (v1_xboole_0 @ X0)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['40', '42'])).
% 0.47/0.65  thf('44', plain,
% 0.47/0.65      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.47/0.65         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify', [status(thm)], ['43'])).
% 0.47/0.65  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('46', plain,
% 0.47/0.65      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify_reflect+', [status(thm)], ['44', '45'])).
% 0.47/0.65  thf('47', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.47/0.65           | ~ (v1_xboole_0 @ X0)
% 0.47/0.65           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['39', '46'])).
% 0.47/0.65  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('49', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.47/0.65      inference('demod', [status(thm)], ['47', '48'])).
% 0.47/0.65  thf('50', plain,
% 0.47/0.65      (![X21 : $i, X22 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X21)
% 0.47/0.65          | ~ (v1_relat_1 @ X22)
% 0.47/0.65          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.47/0.65      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.47/0.65  thf('51', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf(t46_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( v1_relat_1 @ A ) =>
% 0.47/0.65       ( ![B:$i]:
% 0.47/0.65         ( ( v1_relat_1 @ B ) =>
% 0.47/0.65           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.65             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.65  thf('52', plain,
% 0.47/0.65      (![X27 : $i, X28 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X27)
% 0.47/0.65          | ((k1_relat_1 @ (k5_relat_1 @ X28 @ X27)) = (k1_relat_1 @ X28))
% 0.47/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 0.47/0.65          | ~ (v1_relat_1 @ X28))),
% 0.47/0.65      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.47/0.65  thf('53', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65              = (k1_relat_1 @ k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.65  thf('54', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.47/0.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.65  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.47/0.65  thf('56', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.65      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.47/0.65  thf('57', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.47/0.65  thf(fc8_relat_1, axiom,
% 0.47/0.65    (![A:$i]:
% 0.47/0.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.65       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.47/0.65  thf('58', plain,
% 0.47/0.65      (![X23 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (k1_relat_1 @ X23))
% 0.47/0.65          | ~ (v1_relat_1 @ X23)
% 0.47/0.65          | (v1_xboole_0 @ X23))),
% 0.47/0.65      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.47/0.65  thf('59', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.65          | ~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.65  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('61', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.47/0.65  thf('62', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['50', '61'])).
% 0.47/0.65  thf('63', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.47/0.65      inference('sup-', [status(thm)], ['9', '15'])).
% 0.47/0.65  thf('64', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_relat_1 @ X0)
% 0.47/0.65          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.47/0.65          | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.47/0.65  thf('65', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.47/0.65      inference('simplify', [status(thm)], ['64'])).
% 0.47/0.65  thf('66', plain,
% 0.47/0.65      (![X0 : $i, X1 : $i]:
% 0.47/0.65         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.65      inference('sup+', [status(thm)], ['37', '38'])).
% 0.47/0.65  thf('67', plain,
% 0.47/0.65      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.65  thf('68', plain,
% 0.47/0.65      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('split', [status(esa)], ['41'])).
% 0.47/0.65  thf('69', plain,
% 0.47/0.65      ((![X0 : $i]:
% 0.47/0.65          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['67', '68'])).
% 0.47/0.65  thf('70', plain,
% 0.47/0.65      ((![X0 : $i, X1 : $i]:
% 0.47/0.65          (((X0) != (k1_xboole_0))
% 0.47/0.65           | ~ (v1_xboole_0 @ X0)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.65           | ~ (v1_xboole_0 @ X1)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['66', '69'])).
% 0.47/0.65  thf('71', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1)
% 0.47/0.65           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.47/0.65           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.47/0.65  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('73', plain,
% 0.47/0.65      ((![X1 : $i]:
% 0.47/0.65          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('simplify_reflect+', [status(thm)], ['71', '72'])).
% 0.47/0.65  thf('74', plain,
% 0.47/0.65      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.47/0.65         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.47/0.65      inference('sup-', [status(thm)], ['65', '73'])).
% 0.47/0.65  thf('75', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('77', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.65      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.47/0.65  thf('78', plain,
% 0.47/0.65      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.47/0.65       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.47/0.65      inference('split', [status(esa)], ['41'])).
% 0.47/0.65  thf('79', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.47/0.65      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.47/0.65  thf('80', plain,
% 0.47/0.65      (![X0 : $i]:
% 0.47/0.65         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.65      inference('simpl_trail', [status(thm)], ['49', '79'])).
% 0.47/0.65  thf('81', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.65      inference('sup-', [status(thm)], ['36', '80'])).
% 0.47/0.65  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.65  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.65  thf('84', plain, ($false),
% 0.47/0.65      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.47/0.65  
% 0.47/0.65  % SZS output end Refutation
% 0.47/0.65  
% 0.47/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
