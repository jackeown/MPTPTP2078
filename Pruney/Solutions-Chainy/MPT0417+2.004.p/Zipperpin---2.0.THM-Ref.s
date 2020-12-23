%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMnOeMg0h9

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:14 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 199 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  660 (2066 expanded)
%              Number of equality atoms :   55 ( 184 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(t48_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t47_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) )
          = ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X21 @ ( k2_subset_1 @ X21 ) @ ( k5_setfam_1 @ X21 @ X20 ) )
        = ( k6_setfam_1 @ X21 @ ( k7_setfam_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t47_setfam_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('15',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X21 @ ( k5_setfam_1 @ X21 @ X20 ) )
        = ( k6_setfam_1 @ X21 @ ( k7_setfam_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_setfam_1 @ X17 @ ( k7_setfam_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('22',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k6_setfam_1 @ sk_A @ sk_B ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k7_setfam_1 @ X18 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ( k7_setfam_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('33',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X5 @ X4 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['32','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    = ( k6_setfam_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['23','28'])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('45',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ sk_A @ ( k2_subset_1 @ sk_A ) @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k7_subset_1 @ sk_A @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMnOeMg0h9
% 0.16/0.37  % Computer   : n003.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:12:57 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 444 iterations in 0.199s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.48/0.68  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.48/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.68  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.48/0.68  thf(t48_setfam_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.68         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.48/0.68           ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.68            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.48/0.68              ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t48_setfam_1])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(dt_k7_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( m1_subset_1 @
% 0.48/0.68         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (![X14 : $i, X15 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (k7_setfam_1 @ X14 @ X15) @ 
% 0.48/0.68           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.48/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.68  thf(dt_k5_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (![X12 : $i, X13 : $i]:
% 0.48/0.68         ((m1_subset_1 @ (k5_setfam_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.48/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.48/0.68        (k1_zfmisc_1 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.68  thf(involutiveness_k3_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.48/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ 
% 0.48/0.68         (k3_subset_1 @ sk_A @ 
% 0.48/0.68          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.48/0.68         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.48/0.68        (k1_zfmisc_1 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.48/0.68  thf(d5_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X1 : $i, X2 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.48/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ 
% 0.48/0.68         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68         = (k4_xboole_0 @ sk_A @ 
% 0.48/0.68            (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.48/0.68        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.68  thf(t47_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.48/0.68         ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) ) =
% 0.48/0.68           ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X20 : $i, X21 : $i]:
% 0.48/0.68         (((X20) = (k1_xboole_0))
% 0.48/0.68          | ((k7_subset_1 @ X21 @ (k2_subset_1 @ X21) @ 
% 0.48/0.68              (k5_setfam_1 @ X21 @ X20))
% 0.48/0.68              = (k6_setfam_1 @ X21 @ (k7_setfam_1 @ X21 @ X20)))
% 0.48/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.48/0.68      inference('cnf', [status(esa)], [t47_setfam_1])).
% 0.48/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.68  thf('12', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf(dt_k2_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.48/0.68  thf('14', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('15', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.48/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.68  thf(redefinition_k7_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.48/0.68          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.48/0.68      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X20 : $i, X21 : $i]:
% 0.48/0.68         (((X20) = (k1_xboole_0))
% 0.48/0.68          | ((k4_xboole_0 @ X21 @ (k5_setfam_1 @ X21 @ X20))
% 0.48/0.68              = (k6_setfam_1 @ X21 @ (k7_setfam_1 @ X21 @ X20)))
% 0.48/0.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.48/0.68      inference('demod', [status(thm)], ['11', '12', '17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      ((((k4_xboole_0 @ sk_A @ 
% 0.48/0.68          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68          = (k6_setfam_1 @ sk_A @ 
% 0.48/0.68             (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.48/0.68        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '18'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(involutiveness_k7_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X16 : $i, X17 : $i]:
% 0.48/0.68         (((k7_setfam_1 @ X17 @ (k7_setfam_1 @ X17 @ X16)) = (X16))
% 0.48/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 0.48/0.68      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      ((((k4_xboole_0 @ sk_A @ 
% 0.48/0.68          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68          = (k6_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['19', '22'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t46_setfam_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.48/0.68       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.48/0.68            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         (((k7_setfam_1 @ X18 @ X19) != (k1_xboole_0))
% 0.48/0.68          | ((X19) = (k1_xboole_0))
% 0.48/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.48/0.68      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      ((((sk_B) = (k1_xboole_0))
% 0.48/0.68        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.68  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('28', plain, (((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ 
% 0.48/0.68         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ 
% 0.48/0.68         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['9', '29'])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['6', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ 
% 0.48/0.68         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.48/0.68  thf('33', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.48/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.48/0.68  thf(dt_k7_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.48/0.68          | (m1_subset_1 @ (k7_subset_1 @ X5 @ X4 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['33', '34'])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X1 : $i, X2 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.48/0.68          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_subset_1 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1))
% 0.48/0.68           = (k4_xboole_0 @ X0 @ (k7_subset_1 @ X0 @ X0 @ X1)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.48/0.68           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.48/0.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k4_xboole_0 @ sk_A @ 
% 0.48/0.68            (k4_xboole_0 @ sk_A @ 
% 0.48/0.68             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['32', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ 
% 0.48/0.68         (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.48/0.68         = (k6_setfam_1 @ sk_A @ sk_B))),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['23', '28'])).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      (((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['41', '42'])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (((k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['31', '43'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         != (k7_subset_1 @ sk_A @ (k2_subset_1 @ sk_A) @ 
% 0.48/0.68             (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('46', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.48/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         != (k7_subset_1 @ sk_A @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.48/0.68         != (k4_xboole_0 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('demod', [status(thm)], ['47', '48'])).
% 0.48/0.68  thf('50', plain, ($false),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['44', '49'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
