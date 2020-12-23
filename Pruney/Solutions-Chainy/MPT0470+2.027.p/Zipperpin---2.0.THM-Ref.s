%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JJKxvw01Ot

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:30 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 134 expanded)
%              Number of leaves         :   22 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  640 ( 881 expanded)
%              Number of equality atoms :   51 (  82 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('29',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,
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

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X12 ) @ ( k2_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('68',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['31','68'])).

thf('70',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JJKxvw01Ot
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:22:37 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.38  % Number of cores: 8
% 0.23/0.39  % Python version: Python 3.6.8
% 0.23/0.39  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 379 iterations in 0.222s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(cc1_relat_1, axiom,
% 0.49/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.49/0.72  thf('0', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.72  thf(dt_k5_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.49/0.72       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (![X10 : $i, X11 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X11)
% 0.49/0.72          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.49/0.72  thf('2', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.72  thf(t60_relat_1, axiom,
% 0.49/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.72  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf(t45_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( v1_relat_1 @ B ) =>
% 0.49/0.72           ( r1_tarski @
% 0.49/0.72             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X13 : $i, X14 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X13)
% 0.49/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.49/0.72             (k2_relat_1 @ X13))
% 0.49/0.72          | ~ (v1_relat_1 @ X14))),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.72           k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['3', '4'])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.72             k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '5'])).
% 0.49/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.49/0.72  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.72             k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.72  thf('9', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.72  thf(d10_xboole_0, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X1 : $i, X3 : $i]:
% 0.49/0.72         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.49/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['8', '11'])).
% 0.49/0.72  thf(fc3_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X5 : $i, X6 : $i]:
% 0.49/0.72         ((v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.49/0.72  thf(l13_xboole_0, axiom,
% 0.49/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.72  thf(t21_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( r1_tarski @
% 0.49/0.72         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('16', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         ((r1_tarski @ X12 @ 
% 0.49/0.72           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '17'])).
% 0.49/0.72  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['18', '19'])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['1', '20'])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.49/0.72  thf('23', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['0', '22'])).
% 0.49/0.72  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf(t62_relat_1, conjecture,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.49/0.72         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]:
% 0.49/0.72        ( ( v1_relat_1 @ A ) =>
% 0.49/0.72          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.49/0.72            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.49/0.72        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.72      inference('split', [status(esa)], ['29'])).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['28', '30'])).
% 0.49/0.72  thf('32', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      (![X10 : $i, X11 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X11)
% 0.49/0.72          | (v1_relat_1 @ (k5_relat_1 @ X10 @ X11)))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.49/0.72  thf('34', plain, (![X9 : $i]: ((v1_relat_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.72  thf('35', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf(t46_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ A ) =>
% 0.49/0.72       ( ![B:$i]:
% 0.49/0.72         ( ( v1_relat_1 @ B ) =>
% 0.49/0.72           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.49/0.72             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (![X15 : $i, X16 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X15)
% 0.49/0.72          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15)) = (k1_relat_1 @ X16))
% 0.49/0.72          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 0.49/0.72          | ~ (v1_relat_1 @ X16))),
% 0.49/0.72      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.49/0.72  thf('37', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.72              = (k1_relat_1 @ k1_xboole_0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.72  thf('38', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.72  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['34', '40'])).
% 0.49/0.72  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['41', '42'])).
% 0.49/0.72  thf(fc4_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      (![X7 : $i, X8 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ X7) | (v1_xboole_0 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         ((r1_tarski @ X12 @ 
% 0.49/0.72           (k2_zfmisc_1 @ (k1_relat_1 @ X12) @ (k2_relat_1 @ X12)))
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r1_tarski @ X0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['46', '47'])).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['43', '48'])).
% 0.49/0.72  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('51', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.72  thf('52', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['33', '51'])).
% 0.49/0.72  thf('53', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['52'])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['32', '53'])).
% 0.49/0.72  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('56', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | (r1_tarski @ (k5_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['54', '55'])).
% 0.49/0.72  thf('57', plain,
% 0.49/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.72  thf('58', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ X0)
% 0.49/0.72          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.49/0.72      inference('split', [status(esa)], ['29'])).
% 0.49/0.72  thf('61', plain,
% 0.49/0.72      ((![X0 : $i]:
% 0.49/0.72          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['59', '60'])).
% 0.49/0.72  thf('62', plain,
% 0.49/0.72      (((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.72         | ~ (v1_relat_1 @ sk_A)
% 0.49/0.72         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['58', '61'])).
% 0.49/0.72  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('65', plain,
% 0.49/0.72      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.72         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.49/0.72      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.49/0.72  thf('66', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['65'])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.49/0.72       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.49/0.72      inference('split', [status(esa)], ['29'])).
% 0.49/0.72  thf('68', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.49/0.72  thf('69', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['31', '68'])).
% 0.49/0.72  thf('70', plain,
% 0.49/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_A)
% 0.49/0.72        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['27', '69'])).
% 0.49/0.72  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('73', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.49/0.72  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
