%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0nvGNeMP0T

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:44 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  128 (1527 expanded)
%              Number of leaves         :   29 ( 512 expanded)
%              Depth                    :   21
%              Number of atoms          :  822 (10323 expanded)
%              Number of equality atoms :   58 ( 901 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_tarski @ X13 @ X11 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('4',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
       != ( k2_subset_1 @ X29 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X29 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('11',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ ( k2_subset_1 @ X29 ) @ ( k1_zfmisc_1 @ X29 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X29 @ ( k2_subset_1 @ X29 ) ) @ ( k2_subset_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X21 ) @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('14',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('37',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ! [X29: $i] :
      ( r1_tarski @ k1_xboole_0 @ X29 ) ),
    inference(demod,[status(thm)],['11','12','15','16','45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['9','52'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('55',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X25 @ ( k3_subset_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('63',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['61','64'])).

thf('67',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X29 @ X30 ) @ X30 )
      | ( X30
        = ( k2_subset_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf('68',plain,(
    ! [X18: $i] :
      ( ( k2_subset_1 @ X18 )
      = X18 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('69',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X29 @ X30 ) @ X30 )
      | ( X30 = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('72',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('75',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('80',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('83',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( r1_tarski @ X26 @ ( k3_subset_1 @ X27 @ X28 ) )
      | ~ ( r1_tarski @ X28 @ ( k3_subset_1 @ X27 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('90',plain,(
    r1_tarski @ sk_C_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('92',plain,(
    r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['76','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','44'])).

thf('95',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['65','93','94'])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0nvGNeMP0T
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.78  % Solved by: fo/fo7.sh
% 0.55/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.78  % done 652 iterations in 0.324s
% 0.55/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.78  % SZS output start Refutation
% 0.55/0.78  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.55/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.55/0.78  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.55/0.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.78  thf(t40_subset_1, conjecture,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.55/0.78         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.55/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.78    (~( ![A:$i,B:$i,C:$i]:
% 0.55/0.78        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78          ( ( ( r1_tarski @ B @ C ) & 
% 0.55/0.78              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.55/0.78            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.55/0.78    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.55/0.78  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(d2_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ( v1_xboole_0 @ A ) =>
% 0.55/0.78         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.55/0.78       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.78         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.78  thf('1', plain,
% 0.55/0.78      (![X15 : $i, X16 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X15 @ X16)
% 0.55/0.78          | (r2_hidden @ X15 @ X16)
% 0.55/0.78          | (v1_xboole_0 @ X16))),
% 0.55/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.55/0.78  thf('2', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.78        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.55/0.78  thf(d1_zfmisc_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.55/0.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.55/0.78  thf('3', plain,
% 0.55/0.78      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X13 @ X12)
% 0.55/0.78          | (r1_tarski @ X13 @ X11)
% 0.55/0.78          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.55/0.78  thf('4', plain,
% 0.55/0.78      (![X11 : $i, X13 : $i]:
% 0.55/0.78         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['3'])).
% 0.55/0.78  thf('5', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['2', '4'])).
% 0.55/0.78  thf('6', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t1_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i,C:$i]:
% 0.55/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.55/0.78       ( r1_tarski @ A @ C ) ))).
% 0.55/0.78  thf('7', plain,
% 0.55/0.78      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.78         (~ (r1_tarski @ X6 @ X7)
% 0.55/0.78          | ~ (r1_tarski @ X7 @ X8)
% 0.55/0.78          | (r1_tarski @ X6 @ X8))),
% 0.55/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.55/0.78  thf('8', plain,
% 0.55/0.78      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.78  thf('9', plain,
% 0.55/0.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['5', '8'])).
% 0.55/0.78  thf(t39_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.55/0.78         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.55/0.78  thf('10', plain,
% 0.55/0.78      (![X29 : $i, X30 : $i]:
% 0.55/0.78         (((X30) != (k2_subset_1 @ X29))
% 0.55/0.78          | (r1_tarski @ (k3_subset_1 @ X29 @ X30) @ X30)
% 0.55/0.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.55/0.78  thf('11', plain,
% 0.55/0.78      (![X29 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ (k2_subset_1 @ X29) @ (k1_zfmisc_1 @ X29))
% 0.55/0.78          | (r1_tarski @ (k3_subset_1 @ X29 @ (k2_subset_1 @ X29)) @ 
% 0.55/0.78             (k2_subset_1 @ X29)))),
% 0.55/0.78      inference('simplify', [status(thm)], ['10'])).
% 0.55/0.78  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.55/0.78  thf('12', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.78  thf(dt_k2_subset_1, axiom,
% 0.55/0.78    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.78  thf('13', plain,
% 0.55/0.78      (![X21 : $i]: (m1_subset_1 @ (k2_subset_1 @ X21) @ (k1_zfmisc_1 @ X21))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.55/0.78  thf('14', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.78  thf('15', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.55/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('16', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.78  thf(idempotence_k3_xboole_0, axiom,
% 0.55/0.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.55/0.78  thf('17', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.55/0.78      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.78  thf(t100_xboole_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.55/0.78  thf('18', plain,
% 0.55/0.78      (![X4 : $i, X5 : $i]:
% 0.55/0.78         ((k4_xboole_0 @ X4 @ X5)
% 0.55/0.78           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.55/0.78  thf('19', plain,
% 0.55/0.78      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['17', '18'])).
% 0.55/0.78  thf(t92_xboole_1, axiom,
% 0.55/0.78    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.55/0.78  thf('20', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.55/0.78  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.78  thf('22', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.55/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf(dt_k3_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.55/0.78  thf('23', plain,
% 0.55/0.78      (![X22 : $i, X23 : $i]:
% 0.55/0.78         ((m1_subset_1 @ (k3_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.55/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.55/0.78  thf('24', plain,
% 0.55/0.78      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['22', '23'])).
% 0.55/0.78  thf('25', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.55/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf(d5_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.55/0.78  thf('26', plain,
% 0.55/0.78      (![X19 : $i, X20 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.55/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.55/0.78  thf('27', plain,
% 0.55/0.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.78  thf('28', plain,
% 0.55/0.78      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('demod', [status(thm)], ['24', '27'])).
% 0.55/0.78  thf('29', plain,
% 0.55/0.78      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['21', '28'])).
% 0.55/0.78  thf(involutiveness_k3_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.55/0.78  thf('30', plain,
% 0.55/0.78      (![X24 : $i, X25 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.55/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.55/0.78  thf('31', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['29', '30'])).
% 0.55/0.78  thf('32', plain,
% 0.55/0.78      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['21', '28'])).
% 0.55/0.78  thf('33', plain,
% 0.55/0.78      (![X19 : $i, X20 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.55/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.55/0.78  thf('34', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.78  thf('35', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['31', '34'])).
% 0.55/0.78  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.78  thf('37', plain, (![X21 : $i]: (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X21))),
% 0.55/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.55/0.78  thf('38', plain,
% 0.55/0.78      (![X24 : $i, X25 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.55/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.55/0.78  thf('39', plain,
% 0.55/0.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['37', '38'])).
% 0.55/0.78  thf('40', plain,
% 0.55/0.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['25', '26'])).
% 0.55/0.78  thf('41', plain,
% 0.55/0.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.55/0.78      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.78  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['36', '41'])).
% 0.55/0.78  thf('43', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.78  thf('44', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.78      inference('sup+', [status(thm)], ['42', '43'])).
% 0.55/0.78  thf('45', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['35', '44'])).
% 0.55/0.78  thf('46', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.78  thf('47', plain, (![X29 : $i]: (r1_tarski @ k1_xboole_0 @ X29)),
% 0.55/0.78      inference('demod', [status(thm)], ['11', '12', '15', '16', '45', '46'])).
% 0.55/0.78  thf('48', plain,
% 0.55/0.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.55/0.78         (~ (r1_tarski @ X10 @ X11)
% 0.55/0.78          | (r2_hidden @ X10 @ X12)
% 0.55/0.78          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.55/0.78  thf('49', plain,
% 0.55/0.78      (![X10 : $i, X11 : $i]:
% 0.55/0.78         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.55/0.78      inference('simplify', [status(thm)], ['48'])).
% 0.55/0.78  thf('50', plain,
% 0.55/0.78      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['47', '49'])).
% 0.55/0.78  thf(d1_xboole_0, axiom,
% 0.55/0.78    (![A:$i]:
% 0.55/0.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.55/0.78  thf('51', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.78  thf('52', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.55/0.78  thf('53', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.55/0.78      inference('sup-', [status(thm)], ['9', '52'])).
% 0.55/0.78  thf('54', plain,
% 0.55/0.78      (![X10 : $i, X11 : $i]:
% 0.55/0.78         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.55/0.78      inference('simplify', [status(thm)], ['48'])).
% 0.55/0.78  thf('55', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['53', '54'])).
% 0.55/0.78  thf('56', plain,
% 0.55/0.78      (![X15 : $i, X16 : $i]:
% 0.55/0.78         (~ (r2_hidden @ X15 @ X16)
% 0.55/0.78          | (m1_subset_1 @ X15 @ X16)
% 0.55/0.78          | (v1_xboole_0 @ X16))),
% 0.55/0.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.55/0.78  thf('57', plain,
% 0.55/0.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.55/0.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.55/0.78  thf('58', plain,
% 0.55/0.78      (![X15 : $i, X16 : $i]:
% 0.55/0.78         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.55/0.78      inference('clc', [status(thm)], ['56', '57'])).
% 0.55/0.78  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['55', '58'])).
% 0.55/0.78  thf('60', plain,
% 0.55/0.78      (![X24 : $i, X25 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X25 @ (k3_subset_1 @ X25 @ X24)) = (X24))
% 0.55/0.78          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 0.55/0.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.55/0.78  thf('61', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.78  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['55', '58'])).
% 0.55/0.78  thf('63', plain,
% 0.55/0.78      (![X19 : $i, X20 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.55/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.55/0.78  thf('64', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['62', '63'])).
% 0.55/0.78  thf('65', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['61', '64'])).
% 0.55/0.78  thf('66', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['61', '64'])).
% 0.55/0.78  thf('67', plain,
% 0.55/0.78      (![X29 : $i, X30 : $i]:
% 0.55/0.78         (~ (r1_tarski @ (k3_subset_1 @ X29 @ X30) @ X30)
% 0.55/0.78          | ((X30) = (k2_subset_1 @ X29))
% 0.55/0.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.55/0.78  thf('68', plain, (![X18 : $i]: ((k2_subset_1 @ X18) = (X18))),
% 0.55/0.78      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.78  thf('69', plain,
% 0.55/0.78      (![X29 : $i, X30 : $i]:
% 0.55/0.78         (~ (r1_tarski @ (k3_subset_1 @ X29 @ X30) @ X30)
% 0.55/0.78          | ((X30) = (X29))
% 0.55/0.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.55/0.78      inference('demod', [status(thm)], ['67', '68'])).
% 0.55/0.78  thf('70', plain,
% 0.55/0.78      ((~ (r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.55/0.78        | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.78        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['66', '69'])).
% 0.55/0.78  thf('71', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['55', '58'])).
% 0.55/0.78  thf('72', plain,
% 0.55/0.78      (![X22 : $i, X23 : $i]:
% 0.55/0.78         ((m1_subset_1 @ (k3_subset_1 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.55/0.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.55/0.78      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.55/0.78  thf('73', plain,
% 0.55/0.78      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['71', '72'])).
% 0.55/0.78  thf('74', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['62', '63'])).
% 0.55/0.78  thf('75', plain,
% 0.55/0.78      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['73', '74'])).
% 0.55/0.78  thf('76', plain,
% 0.55/0.78      ((~ (r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 0.55/0.78        | ((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.55/0.78      inference('demod', [status(thm)], ['70', '75'])).
% 0.55/0.78  thf('77', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('78', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('79', plain,
% 0.55/0.78      (![X19 : $i, X20 : $i]:
% 0.55/0.78         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.55/0.78          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.55/0.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.55/0.78  thf('80', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.55/0.78  thf('81', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['77', '80'])).
% 0.55/0.78  thf('82', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf(t35_subset_1, axiom,
% 0.55/0.78    (![A:$i,B:$i]:
% 0.55/0.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78       ( ![C:$i]:
% 0.55/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.78           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.55/0.78             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.55/0.78  thf('83', plain,
% 0.55/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.55/0.78          | (r1_tarski @ X26 @ (k3_subset_1 @ X27 @ X28))
% 0.55/0.78          | ~ (r1_tarski @ X28 @ (k3_subset_1 @ X27 @ X26))
% 0.55/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.55/0.78      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.55/0.78  thf('84', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.78          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.55/0.78          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['82', '83'])).
% 0.55/0.78  thf('85', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['78', '79'])).
% 0.55/0.78  thf('86', plain,
% 0.55/0.78      (![X0 : $i]:
% 0.55/0.78         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.55/0.78          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.55/0.78          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.55/0.78      inference('demod', [status(thm)], ['84', '85'])).
% 0.55/0.78  thf('87', plain,
% 0.55/0.78      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.55/0.78        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.55/0.78      inference('sup-', [status(thm)], ['81', '86'])).
% 0.55/0.78  thf('88', plain,
% 0.55/0.78      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['62', '63'])).
% 0.55/0.78  thf('89', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.55/0.78      inference('sup-', [status(thm)], ['55', '58'])).
% 0.55/0.78  thf('90', plain, ((r1_tarski @ sk_C_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.55/0.78  thf('91', plain,
% 0.55/0.78      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.55/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.55/0.78  thf('92', plain, ((r1_tarski @ sk_B_1 @ (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.55/0.78      inference('sup-', [status(thm)], ['90', '91'])).
% 0.55/0.78  thf('93', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (sk_A))),
% 0.55/0.78      inference('demod', [status(thm)], ['76', '92'])).
% 0.55/0.78  thf('94', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.55/0.78      inference('demod', [status(thm)], ['35', '44'])).
% 0.55/0.78  thf('95', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.55/0.78      inference('demod', [status(thm)], ['65', '93', '94'])).
% 0.55/0.78  thf('96', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.55/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.78  thf('97', plain, ($false),
% 0.55/0.78      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 0.55/0.78  
% 0.55/0.78  % SZS output end Refutation
% 0.55/0.78  
% 0.55/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
