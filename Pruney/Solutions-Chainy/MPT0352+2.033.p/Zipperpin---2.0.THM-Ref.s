%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fabll6fcgs

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 208 expanded)
%              Number of leaves         :   22 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  645 (1851 expanded)
%              Number of equality atoms :   37 (  80 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ ( k4_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['21','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ ( k4_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('46',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('48',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','41','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['35','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Fabll6fcgs
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:03:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.55  % Solved by: fo/fo7.sh
% 0.38/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.55  % done 171 iterations in 0.071s
% 0.38/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.55  % SZS output start Refutation
% 0.38/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.55  thf(t31_subset_1, conjecture,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ![C:$i]:
% 0.38/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55           ( ( r1_tarski @ B @ C ) <=>
% 0.38/0.55             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.55    (~( ![A:$i,B:$i]:
% 0.38/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55          ( ![C:$i]:
% 0.38/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55              ( ( r1_tarski @ B @ C ) <=>
% 0.38/0.55                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.55    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.38/0.55  thf('0', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55           (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.55        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('1', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.38/0.55       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d5_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.38/0.55  thf('3', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.38/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.55  thf('4', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('5', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))
% 0.38/0.55        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('6', plain,
% 0.38/0.55      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf(t34_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i,C:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.38/0.55       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.38/0.55  thf('7', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.55          | (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ (k4_xboole_0 @ X8 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.38/0.55  thf('8', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.38/0.55         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.55  thf('9', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['4', '8'])).
% 0.38/0.55  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('11', plain,
% 0.38/0.55      (![X19 : $i, X20 : $i]:
% 0.38/0.55         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.38/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.38/0.55  thf('12', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf('13', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.38/0.55      inference('demod', [status(thm)], ['9', '12'])).
% 0.38/0.55  thf('14', plain,
% 0.38/0.55      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55           (k3_subset_1 @ sk_A @ sk_B)))
% 0.38/0.55         <= (~
% 0.38/0.55             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('15', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.38/0.55       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.55  thf('16', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.38/0.55       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('17', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf(d2_subset_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.38/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.38/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.55  thf('18', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ X17)
% 0.38/0.55          | (r2_hidden @ X16 @ X17)
% 0.38/0.55          | (v1_xboole_0 @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.55  thf('19', plain,
% 0.38/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.55  thf(fc1_subset_1, axiom,
% 0.38/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.55  thf('20', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.38/0.55  thf('21', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.55  thf(d1_zfmisc_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.38/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.38/0.55  thf('22', plain,
% 0.38/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.55         (~ (r2_hidden @ X14 @ X13)
% 0.38/0.55          | (r1_tarski @ X14 @ X12)
% 0.38/0.55          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.38/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.38/0.55  thf('23', plain,
% 0.38/0.55      (![X12 : $i, X14 : $i]:
% 0.38/0.55         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.55  thf('24', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['21', '23'])).
% 0.38/0.55  thf(t28_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.55  thf('25', plain,
% 0.38/0.55      (![X4 : $i, X5 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.55  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.55  thf('27', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.55  thf(t100_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.38/0.55  thf('28', plain,
% 0.38/0.55      (![X2 : $i, X3 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X2 @ X3)
% 0.38/0.55           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.38/0.55  thf('29', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.55  thf('30', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['26', '29'])).
% 0.38/0.55  thf(t48_xboole_1, axiom,
% 0.38/0.55    (![A:$i,B:$i]:
% 0.38/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.55  thf('31', plain,
% 0.38/0.55      (![X9 : $i, X10 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.38/0.55           = (k3_xboole_0 @ X9 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.55  thf('32', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.38/0.55         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.38/0.55  thf('33', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.55  thf('34', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.55  thf('35', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.38/0.55      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.38/0.55  thf('36', plain,
% 0.38/0.55      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B)))
% 0.38/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('split', [status(esa)], ['5'])).
% 0.38/0.55  thf('37', plain,
% 0.38/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.55         (~ (r1_tarski @ X6 @ X7)
% 0.38/0.55          | (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ (k4_xboole_0 @ X8 @ X6)))),
% 0.38/0.55      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.38/0.55  thf('38', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (r1_tarski @ (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B)) @ 
% 0.38/0.55           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.38/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.55  thf('39', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['26', '29'])).
% 0.38/0.55  thf('40', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.55  thf('41', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.38/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.55  thf('42', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.55  thf('43', plain,
% 0.38/0.55      (![X16 : $i, X17 : $i]:
% 0.38/0.55         (~ (m1_subset_1 @ X16 @ X17)
% 0.38/0.55          | (r2_hidden @ X16 @ X17)
% 0.38/0.55          | (v1_xboole_0 @ X17))),
% 0.38/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.38/0.55  thf('44', plain,
% 0.38/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.55        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.55  thf('45', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.38/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.38/0.55  thf('46', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.55      inference('clc', [status(thm)], ['44', '45'])).
% 0.38/0.55  thf('47', plain,
% 0.38/0.55      (![X12 : $i, X14 : $i]:
% 0.38/0.55         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.38/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.55  thf('48', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.38/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.55  thf('49', plain,
% 0.38/0.55      (![X4 : $i, X5 : $i]:
% 0.38/0.55         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.38/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.55  thf('50', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('51', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X0 @ X1)
% 0.38/0.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.38/0.55      inference('sup+', [status(thm)], ['27', '28'])).
% 0.38/0.55  thf('52', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('53', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.55  thf('54', plain,
% 0.38/0.55      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['52', '53'])).
% 0.38/0.55  thf('55', plain,
% 0.38/0.55      ((![X0 : $i]:
% 0.38/0.55          (r1_tarski @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B)) @ 
% 0.38/0.55           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 0.38/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['38', '41', '54'])).
% 0.38/0.55  thf('56', plain,
% 0.38/0.55      (((r1_tarski @ sk_B @ 
% 0.38/0.55         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))))
% 0.38/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('sup+', [status(thm)], ['35', '55'])).
% 0.38/0.55  thf('57', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.38/0.55  thf('58', plain,
% 0.38/0.55      (![X9 : $i, X10 : $i]:
% 0.38/0.55         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.38/0.55           = (k3_xboole_0 @ X9 @ X10))),
% 0.38/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.55  thf('59', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 0.38/0.55         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.38/0.55      inference('sup+', [status(thm)], ['57', '58'])).
% 0.38/0.55  thf('60', plain,
% 0.38/0.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.55  thf('61', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.55  thf('62', plain,
% 0.38/0.55      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_1)) = (sk_C_1))),
% 0.38/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.38/0.55  thf('63', plain,
% 0.38/0.55      (((r1_tarski @ sk_B @ sk_C_1))
% 0.38/0.55         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.38/0.55      inference('demod', [status(thm)], ['56', '62'])).
% 0.38/0.55  thf('64', plain,
% 0.38/0.55      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.38/0.55      inference('split', [status(esa)], ['0'])).
% 0.38/0.55  thf('65', plain,
% 0.38/0.55      (~
% 0.38/0.55       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.38/0.55         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.38/0.55       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.38/0.55      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.55  thf('66', plain, ($false),
% 0.38/0.55      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '65'])).
% 0.38/0.55  
% 0.38/0.55  % SZS output end Refutation
% 0.38/0.55  
% 0.38/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
