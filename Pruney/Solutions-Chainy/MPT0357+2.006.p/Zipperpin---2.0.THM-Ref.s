%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ctg2IRpqlC

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:20 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 117 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  532 ( 951 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k6_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    r2_hidden @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ ( k3_tarski @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('13',plain,(
    r1_tarski @ sk_C @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k6_subset_1 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k6_subset_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( k6_subset_1 @ sk_C @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k6_subset_1 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k6_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ ( k6_subset_1 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k6_subset_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ( r1_tarski @ X23 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_A ) )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_C )
    | ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('49',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['6','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ctg2IRpqlC
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.59  % Solved by: fo/fo7.sh
% 0.40/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.59  % done 363 iterations in 0.131s
% 0.40/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.59  % SZS output start Refutation
% 0.40/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.59  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.40/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.59  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.40/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.59  thf(t36_subset_1, conjecture,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.40/0.59             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.40/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.59    (~( ![A:$i,B:$i]:
% 0.40/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59          ( ![C:$i]:
% 0.40/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59              ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.40/0.59                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ) )),
% 0.40/0.59    inference('cnf.neg', [status(esa)], [t36_subset_1])).
% 0.40/0.59  thf('0', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d5_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.40/0.59  thf('2', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.40/0.59      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.40/0.59  thf(redefinition_k6_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('3', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.59  thf('4', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (((k3_subset_1 @ X14 @ X15) = (k6_subset_1 @ X14 @ X15))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('5', plain,
% 0.40/0.59      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.40/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.59  thf('6', plain, (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.40/0.59      inference('demod', [status(thm)], ['0', '5'])).
% 0.40/0.59  thf('7', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf(d2_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.40/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.40/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.40/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.40/0.59  thf('8', plain,
% 0.40/0.59      (![X11 : $i, X12 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X11 @ X12)
% 0.40/0.59          | (r2_hidden @ X11 @ X12)
% 0.40/0.59          | (v1_xboole_0 @ X12))),
% 0.40/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.40/0.59  thf('9', plain,
% 0.40/0.59      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.59        | (r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.59  thf(fc1_subset_1, axiom,
% 0.40/0.59    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.59  thf('10', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.40/0.59      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.40/0.59  thf('11', plain, ((r2_hidden @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('clc', [status(thm)], ['9', '10'])).
% 0.40/0.59  thf(l49_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.40/0.59  thf('12', plain,
% 0.40/0.59      (![X8 : $i, X9 : $i]:
% 0.40/0.59         ((r1_tarski @ X8 @ (k3_tarski @ X9)) | ~ (r2_hidden @ X8 @ X9))),
% 0.40/0.59      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.40/0.59  thf('13', plain, ((r1_tarski @ sk_C @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.59  thf(t99_zfmisc_1, axiom,
% 0.40/0.59    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.40/0.59  thf('14', plain, (![X10 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X10)) = (X10))),
% 0.40/0.59      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.40/0.59  thf('15', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.40/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.40/0.59  thf(l32_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.59  thf('16', plain,
% 0.40/0.59      (![X2 : $i, X4 : $i]:
% 0.40/0.59         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.40/0.59      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.40/0.59  thf('17', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.59  thf('18', plain,
% 0.40/0.59      (![X2 : $i, X4 : $i]:
% 0.40/0.59         (((k6_subset_1 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.40/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.40/0.59  thf('19', plain, (((k6_subset_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.40/0.59      inference('sup-', [status(thm)], ['15', '18'])).
% 0.40/0.59  thf(t48_xboole_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.59  thf('20', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.40/0.59           = (k3_xboole_0 @ X6 @ X7))),
% 0.40/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.40/0.59  thf('21', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.59  thf('22', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.59  thf('23', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.40/0.59           = (k3_xboole_0 @ X6 @ X7))),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.40/0.59  thf('24', plain,
% 0.40/0.59      (((k6_subset_1 @ sk_C @ k1_xboole_0) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.40/0.59      inference('sup+', [status(thm)], ['19', '23'])).
% 0.40/0.59  thf(t3_boole, axiom,
% 0.40/0.59    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.40/0.59  thf('25', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.40/0.59      inference('cnf', [status(esa)], [t3_boole])).
% 0.40/0.59  thf('26', plain,
% 0.40/0.59      (![X19 : $i, X20 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.40/0.59      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.40/0.59  thf('27', plain, (![X5 : $i]: ((k6_subset_1 @ X5 @ k1_xboole_0) = (X5))),
% 0.40/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.40/0.59  thf('28', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.40/0.59      inference('demod', [status(thm)], ['24', '27'])).
% 0.40/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.59  thf('29', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.59  thf(dt_k6_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.59  thf('30', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.40/0.59  thf('31', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (((k3_subset_1 @ X14 @ X15) = (k6_subset_1 @ X14 @ X15))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('32', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.40/0.59           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.40/0.59  thf('33', plain,
% 0.40/0.59      (![X6 : $i, X7 : $i]:
% 0.40/0.59         ((k6_subset_1 @ X6 @ (k6_subset_1 @ X6 @ X7))
% 0.40/0.59           = (k3_xboole_0 @ X6 @ X7))),
% 0.40/0.59      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.40/0.59  thf('34', plain,
% 0.40/0.59      (![X0 : $i, X1 : $i]:
% 0.40/0.59         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.40/0.59           = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.59  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('36', plain,
% 0.40/0.59      (![X14 : $i, X15 : $i]:
% 0.40/0.59         (((k3_subset_1 @ X14 @ X15) = (k6_subset_1 @ X14 @ X15))
% 0.40/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.40/0.59      inference('demod', [status(thm)], ['2', '3'])).
% 0.40/0.59  thf('37', plain,
% 0.40/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf(t31_subset_1, axiom,
% 0.40/0.59    (![A:$i,B:$i]:
% 0.40/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59       ( ![C:$i]:
% 0.40/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.59           ( ( r1_tarski @ B @ C ) <=>
% 0.40/0.59             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.40/0.59  thf('38', plain,
% 0.40/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.40/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.40/0.59          | ~ (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ 
% 0.40/0.59               (k3_subset_1 @ X22 @ X23))
% 0.40/0.59          | (r1_tarski @ X23 @ X21)
% 0.40/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.40/0.59      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.40/0.59  thf('39', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k3_subset_1 @ sk_A @ X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.59          | (r1_tarski @ X0 @ sk_B)
% 0.40/0.59          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.59  thf('40', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('41', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k3_subset_1 @ sk_A @ X0))
% 0.40/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.40/0.59          | (r1_tarski @ X0 @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.40/0.59  thf('42', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k3_xboole_0 @ sk_A @ X0))
% 0.40/0.59          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_B)
% 0.40/0.59          | ~ (m1_subset_1 @ (k6_subset_1 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.40/0.59      inference('sup-', [status(thm)], ['34', '41'])).
% 0.40/0.59  thf('43', plain,
% 0.40/0.59      (![X16 : $i, X17 : $i]:
% 0.40/0.59         (m1_subset_1 @ (k6_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))),
% 0.40/0.59      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.40/0.59  thf('44', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k3_xboole_0 @ sk_A @ X0))
% 0.40/0.59          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.40/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.59  thf('45', plain,
% 0.40/0.59      (![X0 : $i]:
% 0.40/0.59         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ 
% 0.40/0.59             (k3_xboole_0 @ X0 @ sk_A))
% 0.40/0.59          | (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['29', '44'])).
% 0.40/0.59  thf('46', plain,
% 0.40/0.59      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.40/0.59        | (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['28', '45'])).
% 0.40/0.59  thf('47', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.40/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.59  thf('48', plain,
% 0.40/0.59      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.40/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.59  thf('49', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.40/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.40/0.59  thf('50', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.40/0.59      inference('demod', [status(thm)], ['46', '49'])).
% 0.40/0.59  thf('51', plain, ($false), inference('demod', [status(thm)], ['6', '50'])).
% 0.40/0.59  
% 0.40/0.59  % SZS output end Refutation
% 0.40/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
