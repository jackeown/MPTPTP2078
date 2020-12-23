%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hCI2F86cJ3

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:17 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 426 expanded)
%              Number of leaves         :   18 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  671 (5119 expanded)
%              Number of equality atoms :   42 ( 260 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t33_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
              = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X8 @ X7 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('12',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k4_subset_1 @ X13 @ X12 @ X14 )
        = ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('20',plain,
    ( ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['18','35'])).

thf('37',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X3 @ X4 )
        = ( k4_xboole_0 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) )
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('47',plain,(
    ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X15 @ X17 )
        = ( k4_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k4_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('53',plain,(
    ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('55',plain,(
    ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hCI2F86cJ3
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.33/2.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.33/2.56  % Solved by: fo/fo7.sh
% 2.33/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.56  % done 1339 iterations in 2.109s
% 2.33/2.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.33/2.56  % SZS output start Refutation
% 2.33/2.56  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.33/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.33/2.56  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.33/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.33/2.56  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.56  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.33/2.56  thf(t33_subset_1, conjecture,
% 2.33/2.56    (![A:$i,B:$i]:
% 2.33/2.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56       ( ![C:$i]:
% 2.33/2.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.33/2.56             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.33/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.56    (~( ![A:$i,B:$i]:
% 2.33/2.56        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56          ( ![C:$i]:
% 2.33/2.56            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56              ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.33/2.56                ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ) )),
% 2.33/2.56    inference('cnf.neg', [status(esa)], [t33_subset_1])).
% 2.33/2.56  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(dt_k3_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i]:
% 2.33/2.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.33/2.56  thf('2', plain,
% 2.33/2.56      (![X5 : $i, X6 : $i]:
% 2.33/2.56         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 2.33/2.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.33/2.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.33/2.56  thf('3', plain,
% 2.33/2.56      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['1', '2'])).
% 2.33/2.56  thf('4', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(d5_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i]:
% 2.33/2.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.33/2.56  thf('5', plain,
% 2.33/2.56      (![X3 : $i, X4 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 2.33/2.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.33/2.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.56  thf('6', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.33/2.56      inference('sup-', [status(thm)], ['4', '5'])).
% 2.33/2.56  thf('7', plain,
% 2.33/2.56      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['3', '6'])).
% 2.33/2.56  thf(dt_k4_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i,C:$i]:
% 2.33/2.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.33/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.33/2.56       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.33/2.56  thf('8', plain,
% 2.33/2.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.33/2.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8))
% 2.33/2.56          | (m1_subset_1 @ (k4_subset_1 @ X8 @ X7 @ X9) @ (k1_zfmisc_1 @ X8)))),
% 2.33/2.56      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 2.33/2.56  thf('9', plain,
% 2.33/2.56      (![X0 : $i]:
% 2.33/2.56         ((m1_subset_1 @ 
% 2.33/2.56           (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ X0) @ 
% 2.33/2.56           (k1_zfmisc_1 @ sk_A))
% 2.33/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['7', '8'])).
% 2.33/2.56  thf('10', plain,
% 2.33/2.56      ((m1_subset_1 @ 
% 2.33/2.56        (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['0', '9'])).
% 2.33/2.56  thf('11', plain,
% 2.33/2.56      (![X5 : $i, X6 : $i]:
% 2.33/2.56         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 2.33/2.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 2.33/2.56      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.33/2.56  thf('12', plain,
% 2.33/2.56      ((m1_subset_1 @ 
% 2.33/2.56        (k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['10', '11'])).
% 2.33/2.56  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('14', plain,
% 2.33/2.56      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['3', '6'])).
% 2.33/2.56  thf(redefinition_k4_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i,C:$i]:
% 2.33/2.56     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.33/2.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.33/2.56       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.33/2.56  thf('15', plain,
% 2.33/2.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 2.33/2.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 2.33/2.56          | ((k4_subset_1 @ X13 @ X12 @ X14) = (k2_xboole_0 @ X12 @ X14)))),
% 2.33/2.56      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.33/2.56  thf('16', plain,
% 2.33/2.56      (![X0 : $i]:
% 2.33/2.56         (((k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)
% 2.33/2.56            = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0))
% 2.33/2.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['14', '15'])).
% 2.33/2.56  thf('17', plain,
% 2.33/2.56      (((k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('sup-', [status(thm)], ['13', '16'])).
% 2.33/2.56  thf('18', plain,
% 2.33/2.56      ((m1_subset_1 @ 
% 2.33/2.56        (k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['12', '17'])).
% 2.33/2.56  thf('19', plain,
% 2.33/2.56      ((m1_subset_1 @ 
% 2.33/2.56        (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('sup-', [status(thm)], ['0', '9'])).
% 2.33/2.56  thf('20', plain,
% 2.33/2.56      (((k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('sup-', [status(thm)], ['13', '16'])).
% 2.33/2.56  thf('21', plain,
% 2.33/2.56      ((m1_subset_1 @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['19', '20'])).
% 2.33/2.56  thf('22', plain,
% 2.33/2.56      (![X3 : $i, X4 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 2.33/2.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.33/2.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.56  thf('23', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 2.33/2.56         = (k4_xboole_0 @ sk_A @ 
% 2.33/2.56            (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['21', '22'])).
% 2.33/2.56  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(involutiveness_k3_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i]:
% 2.33/2.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.33/2.56  thf('25', plain,
% 2.33/2.56      (![X10 : $i, X11 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 2.33/2.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.33/2.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.33/2.56  thf('26', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 2.33/2.56      inference('sup-', [status(thm)], ['24', '25'])).
% 2.33/2.56  thf('27', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.33/2.56      inference('sup-', [status(thm)], ['4', '5'])).
% 2.33/2.56  thf('28', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 2.33/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.33/2.56  thf('29', plain,
% 2.33/2.56      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['3', '6'])).
% 2.33/2.56  thf('30', plain,
% 2.33/2.56      (![X3 : $i, X4 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 2.33/2.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.33/2.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.56  thf('31', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B))
% 2.33/2.56         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['29', '30'])).
% 2.33/2.56  thf('32', plain,
% 2.33/2.56      (((sk_B) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.33/2.56      inference('sup+', [status(thm)], ['28', '31'])).
% 2.33/2.56  thf(t41_xboole_1, axiom,
% 2.33/2.56    (![A:$i,B:$i,C:$i]:
% 2.33/2.56     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 2.33/2.56       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.33/2.56  thf('33', plain,
% 2.33/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.56         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 2.33/2.56           = (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 2.33/2.56      inference('cnf', [status(esa)], [t41_xboole_1])).
% 2.33/2.56  thf('34', plain,
% 2.33/2.56      (![X0 : $i]:
% 2.33/2.56         ((k4_xboole_0 @ sk_B @ X0)
% 2.33/2.56           = (k4_xboole_0 @ sk_A @ 
% 2.33/2.56              (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 2.33/2.56      inference('sup+', [status(thm)], ['32', '33'])).
% 2.33/2.56  thf('35', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 2.33/2.56         = (k4_xboole_0 @ sk_B @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['23', '34'])).
% 2.33/2.56  thf('36', plain,
% 2.33/2.56      ((m1_subset_1 @ (k4_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['18', '35'])).
% 2.33/2.56  thf('37', plain,
% 2.33/2.56      (![X3 : $i, X4 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))
% 2.33/2.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.33/2.56      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.33/2.56  thf('38', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['36', '37'])).
% 2.33/2.56  thf('39', plain,
% 2.33/2.56      ((m1_subset_1 @ (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C) @ 
% 2.33/2.56        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('demod', [status(thm)], ['19', '20'])).
% 2.33/2.56  thf('40', plain,
% 2.33/2.56      (![X10 : $i, X11 : $i]:
% 2.33/2.56         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 2.33/2.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.33/2.56      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.33/2.56  thf('41', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k3_subset_1 @ sk_A @ 
% 2.33/2.56          (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)))
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('sup-', [status(thm)], ['39', '40'])).
% 2.33/2.56  thf('42', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ 
% 2.33/2.56         (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))
% 2.33/2.56         = (k4_xboole_0 @ sk_B @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['23', '34'])).
% 2.33/2.56  thf('43', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['41', '42'])).
% 2.33/2.56  thf('44', plain,
% 2.33/2.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('sup+', [status(thm)], ['38', '43'])).
% 2.33/2.56  thf('45', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k7_subset_1 @ sk_A @ sk_B @ sk_C))
% 2.33/2.56         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf('46', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.33/2.56      inference('sup-', [status(thm)], ['4', '5'])).
% 2.33/2.56  thf('47', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k7_subset_1 @ sk_A @ sk_B @ sk_C))
% 2.33/2.56         != (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['45', '46'])).
% 2.33/2.56  thf('48', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.56  thf(redefinition_k7_subset_1, axiom,
% 2.33/2.56    (![A:$i,B:$i,C:$i]:
% 2.33/2.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.33/2.56       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.33/2.56  thf('49', plain,
% 2.33/2.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.33/2.56         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 2.33/2.56          | ((k7_subset_1 @ X16 @ X15 @ X17) = (k4_xboole_0 @ X15 @ X17)))),
% 2.33/2.56      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.33/2.56  thf('50', plain,
% 2.33/2.56      (![X0 : $i]:
% 2.33/2.56         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 2.33/2.56      inference('sup-', [status(thm)], ['48', '49'])).
% 2.33/2.56  thf('51', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         != (k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['47', '50'])).
% 2.33/2.56  thf('52', plain,
% 2.33/2.56      (((k4_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)
% 2.33/2.56         = (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('sup-', [status(thm)], ['13', '16'])).
% 2.33/2.56  thf('53', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['51', '52'])).
% 2.33/2.56  thf('54', plain,
% 2.33/2.56      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))),
% 2.33/2.56      inference('sup-', [status(thm)], ['36', '37'])).
% 2.33/2.56  thf('55', plain,
% 2.33/2.56      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.33/2.56         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C))),
% 2.33/2.56      inference('demod', [status(thm)], ['53', '54'])).
% 2.33/2.56  thf('56', plain, ($false),
% 2.33/2.56      inference('simplify_reflect-', [status(thm)], ['44', '55'])).
% 2.33/2.56  
% 2.33/2.56  % SZS output end Refutation
% 2.33/2.56  
% 2.33/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
