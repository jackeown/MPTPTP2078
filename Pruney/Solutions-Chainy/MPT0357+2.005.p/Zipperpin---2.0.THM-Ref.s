%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3MH0LwDVP2

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:20 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 225 expanded)
%              Number of leaves         :   25 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :  624 (1845 expanded)
%              Number of equality atoms :   41 ( 111 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t36_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
             => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k4_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r1_tarski @ X11 @ X9 )
      | ( X10
       != ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X20: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_tarski @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('34',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('36',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ( r1_tarski @ ( k3_subset_1 @ X24 @ X23 ) @ ( k3_subset_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k6_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k6_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('51',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X16 @ X17 )
        = ( k6_subset_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('56',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('64',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['44','51','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['23','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3MH0LwDVP2
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:50:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 487 iterations in 0.171s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.61  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(t36_subset_1, conjecture,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61       ( ![C:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.43/0.61             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i,B:$i]:
% 0.43/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61          ( ![C:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61              ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.43/0.61                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t36_subset_1])).
% 0.43/0.61  thf('0', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d5_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (((k3_subset_1 @ X16 @ X17) = (k4_xboole_0 @ X16 @ X17))
% 0.43/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.43/0.61  thf(redefinition_k6_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 0.43/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('5', plain,
% 0.43/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.43/0.61  thf('6', plain, (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.43/0.61      inference('demod', [status(thm)], ['0', '5'])).
% 0.43/0.61  thf('7', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(d2_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X13 @ X14)
% 0.43/0.61          | (r2_hidden @ X13 @ X14)
% 0.43/0.61          | (v1_xboole_0 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.61  thf(fc1_subset_1, axiom,
% 0.43/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.61  thf('10', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.43/0.61  thf('11', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['9', '10'])).
% 0.43/0.61  thf(d1_zfmisc_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.43/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X11 @ X10)
% 0.43/0.61          | (r1_tarski @ X11 @ X9)
% 0.43/0.61          | ((X10) != (k1_zfmisc_1 @ X9)))),
% 0.43/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X9 : $i, X11 : $i]:
% 0.43/0.61         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.43/0.61  thf('14', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['11', '13'])).
% 0.43/0.61  thf(t28_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (![X4 : $i, X5 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.61  thf('16', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.43/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.43/0.61  thf('17', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf(t100_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X2 @ X3)
% 0.43/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      (![X2 : $i, X3 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X2 @ X3)
% 0.43/0.61           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.43/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X0 @ X1)
% 0.43/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['17', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['16', '21'])).
% 0.43/0.61  thf('23', plain, (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '22'])).
% 0.43/0.61  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      (![X13 : $i, X14 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X13 @ X14)
% 0.43/0.61          | (r2_hidden @ X13 @ X14)
% 0.43/0.61          | (v1_xboole_0 @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.61  thf('27', plain, (![X20 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.43/0.61  thf('28', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('clc', [status(thm)], ['26', '27'])).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X9 : $i, X11 : $i]:
% 0.43/0.61         ((r1_tarski @ X11 @ X9) | ~ (r2_hidden @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.43/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.43/0.61  thf('30', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      (![X4 : $i, X5 : $i]:
% 0.43/0.61         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.43/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.43/0.61  thf('32', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X0 @ X1)
% 0.43/0.61           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.43/0.61      inference('sup+', [status(thm)], ['17', '20'])).
% 0.43/0.61  thf('34', plain,
% 0.43/0.61      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf(dt_k6_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.43/0.61  thf('35', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k6_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      ((m1_subset_1 @ (k5_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.43/0.61  thf('37', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t31_subset_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61       ( ![C:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.61           ( ( r1_tarski @ B @ C ) <=>
% 0.43/0.61             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.43/0.61          | ~ (r1_tarski @ X25 @ X23)
% 0.43/0.61          | (r1_tarski @ (k3_subset_1 @ X24 @ X23) @ (k3_subset_1 @ X24 @ X25))
% 0.43/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.43/0.61             (k3_subset_1 @ sk_A @ X0))
% 0.43/0.61          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k6_subset_1 @ sk_A @ sk_C_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['1', '4'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61          | (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C_1) @ 
% 0.43/0.61             (k3_subset_1 @ sk_A @ X0))
% 0.43/0.61          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['39', '40'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((k6_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.43/0.61      inference('sup+', [status(thm)], ['16', '21'])).
% 0.43/0.61  thf('43', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.43/0.61          | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.61             (k3_subset_1 @ sk_A @ X0))
% 0.43/0.61          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.43/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C_1)
% 0.43/0.61        | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 0.43/0.61           (k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['36', '43'])).
% 0.43/0.61  thf('45', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('47', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 0.43/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('48', plain,
% 0.43/0.61      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.43/0.61  thf('49', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_C_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['45', '48'])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf('51', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_C_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (((k6_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['32', '33'])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i]:
% 0.43/0.61         (m1_subset_1 @ (k6_subset_1 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))),
% 0.43/0.61      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.43/0.61  thf('54', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (((k3_subset_1 @ X16 @ X17) = (k6_subset_1 @ X16 @ X17))
% 0.43/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.43/0.61      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.43/0.61           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf(t48_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.43/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.43/0.61      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.43/0.61           = (k3_xboole_0 @ X6 @ X7))),
% 0.43/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]:
% 0.43/0.61         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.43/0.61           = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('demod', [status(thm)], ['55', '59'])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.43/0.61         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.43/0.61      inference('sup+', [status(thm)], ['52', '60'])).
% 0.43/0.61  thf('62', plain,
% 0.43/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.43/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.43/0.61  thf('63', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (((k3_subset_1 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.43/0.61      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.43/0.61  thf('65', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.43/0.61      inference('demod', [status(thm)], ['44', '51', '64'])).
% 0.43/0.61  thf('66', plain, ($false), inference('demod', [status(thm)], ['23', '65'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
