%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FVL3hsGbG7

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 149 expanded)
%              Number of leaves         :   28 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  618 (1569 expanded)
%              Number of equality atoms :   46 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t12_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( ( k5_setfam_1 @ X23 @ ( k7_setfam_1 @ X23 @ X22 ) )
        = ( k7_subset_1 @ X23 @ ( k2_subset_1 @ X23 ) @ ( k6_setfam_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t48_setfam_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( ( k5_setfam_1 @ X23 @ ( k7_setfam_1 @ X23 @ X22 ) )
        = ( k7_subset_1 @ X23 @ X23 @ ( k6_setfam_1 @ X23 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ sk_A @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k6_setfam_1 @ A @ B )
        = ( k1_setfam_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k6_setfam_1 @ X21 @ X20 )
        = ( k1_setfam_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_setfam_1])).

thf('7',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_subset_1 @ X12 @ X13 @ ( k3_subset_1 @ X12 @ X13 ) )
        = ( k2_subset_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_subset_1 @ X12 @ X13 @ ( k3_subset_1 @ X12 @ X13 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('28',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('31',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
    = ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('33',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','33'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      = ( k4_xboole_0 @ sk_A @ ( k1_setfam_1 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k1_setfam_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k6_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_setfam_1])).

thf('44',plain,(
    m1_subset_1 @ ( k6_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_setfam_1 @ sk_A @ sk_B )
    = ( k1_setfam_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    m1_subset_1 @ ( k1_setfam_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ ( k1_setfam_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k1_setfam_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k1_setfam_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FVL3hsGbG7
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 87 iterations in 0.050s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.49  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(t12_tops_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.50           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.50              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t48_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.50           ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (((X22) = (k1_xboole_0))
% 0.20/0.50          | ((k5_setfam_1 @ X23 @ (k7_setfam_1 @ X23 @ X22))
% 0.20/0.50              = (k7_subset_1 @ X23 @ (k2_subset_1 @ X23) @ 
% 0.20/0.50                 (k6_setfam_1 @ X23 @ X22)))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.20/0.50      inference('cnf', [status(esa)], [t48_setfam_1])).
% 0.20/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.50  thf('2', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (((X22) = (k1_xboole_0))
% 0.20/0.50          | ((k5_setfam_1 @ X23 @ (k7_setfam_1 @ X23 @ X22))
% 0.20/0.50              = (k7_subset_1 @ X23 @ X23 @ (k6_setfam_1 @ X23 @ X22)))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23))))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50          = (k7_subset_1 @ sk_A @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k6_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( k6_setfam_1 @ A @ B ) = ( k1_setfam_1 @ B ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (((k6_setfam_1 @ X21 @ X20) = (k1_setfam_1 @ X20))
% 0.20/0.50          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_setfam_1])).
% 0.20/0.50  thf('7', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k3_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.20/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ (k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (((k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((m1_subset_1 @ (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k4_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7))
% 0.20/0.50          | (m1_subset_1 @ (k4_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ X0) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((m1_subset_1 @ 
% 0.20/0.50        (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t25_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.50         ( k2_subset_1 @ A ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k4_subset_1 @ X12 @ X13 @ (k3_subset_1 @ X12 @ X13))
% 0.20/0.50            = (k2_subset_1 @ X12))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.20/0.50  thf('21', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k4_subset_1 @ X12 @ X13 @ (k3_subset_1 @ X12 @ X13)) = (X12))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '25'])).
% 0.20/0.50  thf(dt_k5_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k5_setfam_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.20/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '25'])).
% 0.20/0.50  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50         = (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf(t99_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.50  thf('32', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.50  thf('33', plain, (((k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '33'])).
% 0.20/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.50          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_subset_1 @ sk_A @ sk_A @ X0) = (k4_xboole_0 @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50          = (k4_xboole_0 @ sk_A @ (k1_setfam_1 @ sk_B)))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '7', '36'])).
% 0.20/0.50  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k3_subset_1 @ sk_A @ (k1_setfam_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k6_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k6_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k6_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_setfam_1])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((m1_subset_1 @ (k6_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, (((k6_setfam_1 @ sk_A @ sk_B) = (k1_setfam_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_setfam_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((k3_subset_1 @ sk_A @ (k1_setfam_1 @ sk_B))
% 0.20/0.50         = (k4_xboole_0 @ sk_A @ (k1_setfam_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k4_xboole_0 @ sk_A @ (k1_setfam_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '48'])).
% 0.20/0.50  thf('50', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38', '49'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
