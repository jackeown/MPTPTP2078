%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0350+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y622HUTP53

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:45 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 419 expanded)
%              Number of leaves         :   27 ( 134 expanded)
%              Depth                    :   16
%              Number of atoms          :  756 (3586 expanded)
%              Number of equality atoms :   63 ( 240 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( r1_tarski @ X5 @ X3 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ( m1_subset_1 @ X9 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X25: $i] :
      ( ( X25 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_xboole_0 = sk_B )
    | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('30',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( k1_xboole_0 = sk_B ) ),
    inference(clc,[status(thm)],['24','33'])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('36',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('38',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('39',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('41',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ( sk_A != sk_A )
    | ( k1_xboole_0 = sk_B ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    k1_xboole_0 = sk_B ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['41','46'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('53',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X11 @ X12 )
        = ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k1_xboole_0 = sk_A )
    | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('63',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( k1_xboole_0 = sk_A ) ),
    inference(clc,[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k2_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('73',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( sk_A
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['41','46'])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ( k1_xboole_0 = sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    k1_xboole_0 = sk_A ),
    inference(simplify,[status(thm)],['75'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('77',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('80',plain,(
    ! [X21: $i] :
      ( ( k2_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    k1_xboole_0 = sk_A ),
    inference(simplify,[status(thm)],['75'])).

thf('83',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','76','77','78','81','82'])).

thf('84',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','83'])).


%------------------------------------------------------------------------------
