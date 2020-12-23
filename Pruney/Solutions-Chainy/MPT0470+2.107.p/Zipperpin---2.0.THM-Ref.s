%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ytHCOGdo84

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:42 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 141 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  587 ( 927 expanded)
%              Number of equality atoms :   51 ( 102 expanded)
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

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','10','11'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
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
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

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

thf('24',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('31',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X18: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','9'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('61',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['29','61'])).

thf('63',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ytHCOGdo84
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:40:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 205 iterations in 0.122s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.57  thf(dt_k5_relat_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.36/0.57       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X15)
% 0.36/0.57          | ~ (v1_relat_1 @ X16)
% 0.36/0.57          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.36/0.57  thf(t60_relat_1, axiom,
% 0.36/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.57  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.57  thf(t46_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( v1_relat_1 @ B ) =>
% 0.36/0.57           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.57             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (![X21 : $i, X22 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X21)
% 0.36/0.57          | ((k1_relat_1 @ (k5_relat_1 @ X22 @ X21)) = (k1_relat_1 @ X22))
% 0.36/0.57          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ (k1_relat_1 @ X21))
% 0.36/0.57          | ~ (v1_relat_1 @ X22))),
% 0.36/0.57      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.57          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57              = (k1_relat_1 @ k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.57  thf('4', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.36/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.57  thf(d1_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.36/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (![X12 : $i]: ((v1_relat_1 @ X12) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.36/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.36/0.57  thf(t113_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.36/0.57  thf(t152_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.36/0.57  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '9'])).
% 0.36/0.57  thf('11', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['3', '4', '10', '11'])).
% 0.36/0.57  thf(fc8_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.36/0.57       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (![X17 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ (k1_relat_1 @ X17))
% 0.36/0.57          | ~ (v1_relat_1 @ X17)
% 0.36/0.57          | (v1_xboole_0 @ X17))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.57  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['14', '15'])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['0', '16'])).
% 0.36/0.57  thf('18', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '9'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.36/0.57  thf(l13_xboole_0, axiom,
% 0.36/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf(t62_relat_1, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( v1_relat_1 @ A ) =>
% 0.36/0.57          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.36/0.57            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.36/0.57        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.57      inference('split', [status(esa)], ['24'])).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          (((X0) != (k1_xboole_0))
% 0.36/0.57           | ~ (v1_xboole_0 @ X0)
% 0.36/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 0.36/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['23', '25'])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.36/0.57         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.57  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.36/0.57      inference('simplify_reflect+', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X15 : $i, X16 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X15)
% 0.36/0.57          | ~ (v1_relat_1 @ X16)
% 0.36/0.57          | (v1_relat_1 @ (k5_relat_1 @ X15 @ X16)))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.36/0.57  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.57  thf(t45_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( v1_relat_1 @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( v1_relat_1 @ B ) =>
% 0.36/0.57           ( r1_tarski @
% 0.36/0.57             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X19)
% 0.36/0.57          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.36/0.57             (k2_relat_1 @ X19))
% 0.36/0.57          | ~ (v1_relat_1 @ X20))),
% 0.36/0.57      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.36/0.57           k1_xboole_0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.36/0.57      inference('sup+', [status(thm)], ['31', '32'])).
% 0.36/0.57  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '9'])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.36/0.57           k1_xboole_0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.36/0.57  thf('36', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.36/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.57  thf(d10_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X1 : $i, X3 : $i]:
% 0.36/0.57         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.36/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf('39', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['35', '38'])).
% 0.36/0.57  thf(fc9_relat_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.36/0.57       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.36/0.57  thf('40', plain,
% 0.36/0.57      (![X18 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ (k2_relat_1 @ X18))
% 0.36/0.57          | ~ (v1_relat_1 @ X18)
% 0.36/0.57          | (v1_xboole_0 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.57  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.57          | ~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '43'])).
% 0.36/0.57  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.57      inference('sup-', [status(thm)], ['5', '9'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (v1_relat_1 @ X0)
% 0.36/0.57          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.36/0.57          | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('split', [status(esa)], ['24'])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      ((![X0 : $i, X1 : $i]:
% 0.36/0.57          (((X0) != (k1_xboole_0))
% 0.36/0.57           | ~ (v1_xboole_0 @ X0)
% 0.36/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.36/0.57           | ~ (v1_xboole_0 @ X1)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['48', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      ((![X1 : $i]:
% 0.36/0.57          (~ (v1_xboole_0 @ X1)
% 0.36/0.57           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.36/0.57           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('simplify', [status(thm)], ['52'])).
% 0.36/0.57  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      ((![X1 : $i]:
% 0.36/0.57          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('simplify_reflect+', [status(thm)], ['53', '54'])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.36/0.57         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '55'])).
% 0.36/0.57  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.57  thf('59', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.36/0.57      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.36/0.57       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.36/0.57      inference('split', [status(esa)], ['24'])).
% 0.36/0.57  thf('61', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf('62', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['29', '61'])).
% 0.36/0.57  thf('63', plain, (~ (v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '62'])).
% 0.36/0.57  thf('64', plain, ((v1_relat_1 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('65', plain, ($false), inference('demod', [status(thm)], ['63', '64'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
