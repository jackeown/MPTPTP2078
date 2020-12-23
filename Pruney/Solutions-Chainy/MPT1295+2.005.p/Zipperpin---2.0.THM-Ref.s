%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JjFKNaesJ5

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 148 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  626 (1576 expanded)
%              Number of equality atoms :   46 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t11_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) )
          = ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X19 @ ( k2_subset_1 @ X19 ) @ ( k5_setfam_1 @ X19 @ X18 ) )
        = ( k6_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t47_setfam_1])).

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
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X19 @ X19 @ ( k5_setfam_1 @ X19 @ X18 ) )
        = ( k6_setfam_1 @ X19 @ ( k7_setfam_1 @ X19 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k7_subset_1 @ sk_A @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k5_setfam_1 @ X17 @ X16 )
        = ( k3_tarski @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('7',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
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

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('20',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_subset_1 @ X12 @ X13 @ ( k3_subset_1 @ X12 @ X13 ) )
        = ( k2_subset_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_subset_1 @ X12 @ X13 @ ( k3_subset_1 @ X12 @ X13 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k3_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('30',plain,
    ( ( k4_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) @ sk_B ) )
    = ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('31',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k5_setfam_1 @ X17 @ X16 )
        = ( k3_tarski @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('33',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
    = ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('35',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','35'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_A @ X0 )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','38'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('43',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('46',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('48',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_tarski @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JjFKNaesJ5
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:01:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 87 iterations in 0.061s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.50  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(t11_tops_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.50           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50            ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.50              ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t11_tops_2])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t47_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.50         ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) ) =
% 0.20/0.50           ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((X18) = (k1_xboole_0))
% 0.20/0.50          | ((k7_subset_1 @ X19 @ (k2_subset_1 @ X19) @ 
% 0.20/0.50              (k5_setfam_1 @ X19 @ X18))
% 0.20/0.50              = (k6_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.50      inference('cnf', [status(esa)], [t47_setfam_1])).
% 0.20/0.50  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.50  thf('2', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((X18) = (k1_xboole_0))
% 0.20/0.50          | ((k7_subset_1 @ X19 @ X19 @ (k5_setfam_1 @ X19 @ X18))
% 0.20/0.50              = (k6_setfam_1 @ X19 @ (k7_setfam_1 @ X19 @ X18)))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.50      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((((k7_subset_1 @ sk_A @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50          = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k5_setfam_1 @ X17 @ X16) = (k3_tarski @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.50  thf('7', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
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
% 0.20/0.50  thf(dt_k5_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k5_setfam_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((m1_subset_1 @ 
% 0.20/0.50        (k5_setfam_1 @ sk_A @ 
% 0.20/0.50         (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50          (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))) @ 
% 0.20/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t25_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.20/0.50         ( k2_subset_1 @ A ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k4_subset_1 @ X12 @ X13 @ (k3_subset_1 @ X12 @ X13))
% 0.20/0.50            = (k2_subset_1 @ X12))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.20/0.50  thf('23', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (((k4_subset_1 @ X12 @ X13 @ (k3_subset_1 @ X12 @ X13)) = (X12))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.50      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((k3_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B)
% 0.20/0.50         = (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)) @ 
% 0.20/0.50        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((m1_subset_1 @ 
% 0.20/0.50        (k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (((k4_subset_1 @ (k1_zfmisc_1 @ sk_A) @ sk_B @ 
% 0.20/0.50         (k4_xboole_0 @ (k1_zfmisc_1 @ sk_A) @ sk_B)) = (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((m1_subset_1 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (((k5_setfam_1 @ X17 @ X16) = (k3_tarski @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50         = (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf(t99_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.20/0.50  thf('35', plain, (((k5_setfam_1 @ sk_A @ (k1_zfmisc_1 @ sk_A)) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '35'])).
% 0.20/0.50  thf(redefinition_k7_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.20/0.50          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k7_subset_1 @ sk_A @ sk_A @ X0) = (k4_xboole_0 @ sk_A @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((k4_xboole_0 @ sk_A @ (k3_tarski @ sk_B))
% 0.20/0.50          = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.50        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '7', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k3_subset_1 @ sk_A @ (k3_tarski @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k5_setfam_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, (((k5_setfam_1 @ sk_A @ sk_B) = (k3_tarski @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('48', plain, ((m1_subset_1 @ (k3_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.20/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((k3_subset_1 @ sk_A @ (k3_tarski @ sk_B))
% 0.20/0.50         = (k4_xboole_0 @ sk_A @ (k3_tarski @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50         != (k4_xboole_0 @ sk_A @ (k3_tarski @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '50'])).
% 0.20/0.50  thf('52', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['39', '40', '51'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
