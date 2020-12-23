%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ex6QCYekB2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:34 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 127 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   21
%              Number of atoms          :  623 ( 860 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
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

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k1_subset_1 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( r1_tarski @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t62_xboole_1,axiom,(
    ! [A: $i] :
      ~ ( r2_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X4: $i] :
      ~ ( r2_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

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

thf('28',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('33',plain,
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

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( r1_tarski @ X13 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X13 ) @ ( k2_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ~ ( r2_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t62_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('57',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('62',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','62'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ex6QCYekB2
% 0.17/0.37  % Computer   : n024.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.23/0.37  % CPULimit   : 60
% 0.23/0.37  % DateTime   : Tue Dec  1 17:17:21 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.23/0.37  % Running portfolio for 600 s
% 0.23/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 242 iterations in 0.116s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.40/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.40/0.60  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(cc1_relat_1, axiom,
% 0.40/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.40/0.60  thf('0', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf(dt_k5_relat_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.40/0.60       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X11)
% 0.40/0.60          | ~ (v1_relat_1 @ X12)
% 0.40/0.60          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.60  thf('2', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf(t60_relat_1, axiom,
% 0.40/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf(t47_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.40/0.60             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X16)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X16 @ X17)) = (k2_relat_1 @ X17))
% 0.40/0.60          | ~ (r1_tarski @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.40/0.60          | ~ (v1_relat_1 @ X17))),
% 0.40/0.60      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.40/0.60              = (k2_relat_1 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.40/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.60  thf('6', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.60  thf('7', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '8'])).
% 0.40/0.60  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('10', plain, (![X8 : $i]: ((k1_subset_1 @ X8) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.60  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.40/0.60  thf('11', plain, (![X9 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X9))),
% 0.40/0.60      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.40/0.60  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['9', '12'])).
% 0.40/0.60  thf(t21_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( r1_tarski @
% 0.40/0.60         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X13 : $i]:
% 0.40/0.60         ((r1_tarski @ X13 @ 
% 0.40/0.60           (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.40/0.60          | ~ (v1_relat_1 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.40/0.60           (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.40/0.60            k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.40/0.60  thf(t113_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X6 : $i, X7 : $i]:
% 0.40/0.60         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['15', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '18'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '20'])).
% 0.40/0.60  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.60      inference('demod', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf(d8_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.40/0.60       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i, X2 : $i]:
% 0.40/0.60         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.60      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.60          | (r2_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.60  thf(t62_xboole_1, axiom, (![A:$i]: ( ~( r2_xboole_0 @ A @ k1_xboole_0 ) ))).
% 0.40/0.60  thf('26', plain, (![X4 : $i]: ~ (r2_xboole_0 @ X4 @ k1_xboole_0)),
% 0.40/0.60      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('clc', [status(thm)], ['25', '26'])).
% 0.40/0.60  thf(t62_relat_1, conjecture,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i]:
% 0.40/0.60        ( ( v1_relat_1 @ A ) =>
% 0.40/0.60          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.40/0.60        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.60         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['28'])).
% 0.40/0.60  thf('30', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X11 : $i, X12 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X11)
% 0.40/0.60          | ~ (v1_relat_1 @ X12)
% 0.40/0.60          | (v1_relat_1 @ (k5_relat_1 @ X11 @ X12)))),
% 0.40/0.60      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.40/0.60  thf('32', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.40/0.60      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.40/0.60  thf('33', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf(t46_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ( v1_relat_1 @ B ) =>
% 0.40/0.60           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.40/0.60             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (![X14 : $i, X15 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X14)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ X15 @ X14)) = (k1_relat_1 @ X15))
% 0.40/0.60          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X14))
% 0.40/0.60          | ~ (v1_relat_1 @ X15))),
% 0.40/0.60      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.40/0.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.40/0.60              = (k1_relat_1 @ k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.40/0.60  thf('36', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.40/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.60  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('38', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['32', '38'])).
% 0.40/0.60  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (~ (v1_relat_1 @ X0)
% 0.40/0.60          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X13 : $i]:
% 0.40/0.60         ((r1_tarski @ X13 @ 
% 0.40/0.60           (k2_zfmisc_1 @ (k1_relat_1 @ X13) @ (k2_relat_1 @ X13)))
% 0.40/0.60          | ~ (v1_relat_1 @ X13))),
% 0.40/0.60      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ 
% 0.40/0.60           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 0.40/0.60            (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))
% 0.40/0.60          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['41', '42'])).
% 0.40/0.61  thf('44', plain,
% 0.40/0.61      (![X6 : $i, X7 : $i]:
% 0.40/0.61         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.40/0.61      inference('demod', [status(thm)], ['43', '45'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '46'])).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.40/0.61          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.61          | ~ (v1_relat_1 @ X0)
% 0.40/0.61          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['30', '48'])).
% 0.40/0.61  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('sup+', [status(thm)], ['10', '11'])).
% 0.40/0.61  thf('51', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (![X0 : $i, X2 : $i]:
% 0.40/0.61         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.61      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_relat_1 @ X0)
% 0.40/0.61          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.61          | (r2_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.40/0.61  thf('54', plain, (![X4 : $i]: ~ (r2_xboole_0 @ X4 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [t62_xboole_1])).
% 0.40/0.61  thf('55', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.40/0.61          | ~ (v1_relat_1 @ X0))),
% 0.40/0.61      inference('clc', [status(thm)], ['53', '54'])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.40/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.61      inference('split', [status(esa)], ['28'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.40/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.61  thf('58', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.40/0.61         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['57', '58'])).
% 0.40/0.61  thf('60', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['59'])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.40/0.61       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('split', [status(esa)], ['28'])).
% 0.40/0.61  thf('62', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.40/0.61  thf('63', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['29', '62'])).
% 0.40/0.61  thf('64', plain,
% 0.40/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['27', '63'])).
% 0.40/0.61  thf('65', plain, ((v1_relat_1 @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('66', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['64', '65'])).
% 0.40/0.61  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
