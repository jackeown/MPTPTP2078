%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ey2qjgEbWm

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:18 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 138 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  531 (1235 expanded)
%              Number of equality atoms :   31 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t35_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
             => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('23',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X23 @ ( k3_subset_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('31',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['34','39'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_xboole_0 @ X12 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ ( k4_xboole_0 @ X0 @ sk_B ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','53'])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('56',plain,(
    r1_tarski @ sk_C @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['20','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ey2qjgEbWm
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:52:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 593 iterations in 0.215s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.67  thf(t35_subset_1, conjecture,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( ![C:$i]:
% 0.47/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.47/0.67             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i]:
% 0.47/0.67        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67          ( ![C:$i]:
% 0.47/0.67            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67              ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.47/0.67                ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t35_subset_1])).
% 0.47/0.67  thf('0', plain, (~ (r1_tarski @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(involutiveness_k3_subset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (![X22 : $i, X23 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.47/0.67          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.47/0.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.67  thf('4', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(dt_k3_subset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k3_subset_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))
% 0.47/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['4', '5'])).
% 0.47/0.67  thf(d5_subset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.47/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.67         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.67  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.47/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.67  thf(t48_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X10 : $i, X11 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.47/0.67           = (k3_xboole_0 @ X10 @ X11))),
% 0.47/0.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.67         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.67         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['8', '13'])).
% 0.47/0.67  thf('15', plain, (((sk_B) = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['3', '14'])).
% 0.47/0.67  thf(t100_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X3 : $i, X4 : $i]:
% 0.47/0.67         ((k4_xboole_0 @ X3 @ X4)
% 0.47/0.67           = (k5_xboole_0 @ X3 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.47/0.67  thf('20', plain, (~ (r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['0', '19'])).
% 0.47/0.67  thf('21', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('22', plain,
% 0.47/0.67      (![X20 : $i, X21 : $i]:
% 0.47/0.67         ((m1_subset_1 @ (k3_subset_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20))
% 0.47/0.67          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.47/0.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('sup-', [status(thm)], ['21', '22'])).
% 0.47/0.67  thf('24', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.47/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.67  thf('25', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.47/0.67         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.67  thf('26', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      (![X22 : $i, X23 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X23 @ (k3_subset_1 @ X23 @ X22)) = (X22))
% 0.47/0.67          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.47/0.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.47/0.67      inference('demod', [status(thm)], ['25', '28'])).
% 0.47/0.67  thf(t36_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.47/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.67  thf('31', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.47/0.67      inference('sup+', [status(thm)], ['29', '30'])).
% 0.47/0.67  thf(d10_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.67  thf('34', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('35', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('36', plain,
% 0.47/0.67      (![X18 : $i, X19 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.47/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.67  thf('37', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.67  thf(t106_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.47/0.67       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.47/0.67  thf('38', plain,
% 0.47/0.67      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.47/0.67         ((r1_xboole_0 @ X5 @ X7)
% 0.47/0.67          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.47/0.67          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.67  thf('40', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.47/0.67      inference('sup-', [status(thm)], ['34', '39'])).
% 0.47/0.67  thf(t86_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.47/0.67       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.47/0.67  thf('41', plain,
% 0.47/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X15 @ X16)
% 0.47/0.67          | ~ (r1_xboole_0 @ X15 @ X17)
% 0.47/0.67          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.47/0.67  thf('42', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))
% 0.47/0.67          | ~ (r1_tarski @ sk_B @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.67  thf('43', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['33', '42'])).
% 0.47/0.67  thf('44', plain,
% 0.47/0.67      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.47/0.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.67  thf('45', plain,
% 0.47/0.67      (![X0 : $i, X2 : $i]:
% 0.47/0.67         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.67      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.67  thf('46', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.47/0.67          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.67  thf('47', plain, (((sk_B) = (k4_xboole_0 @ sk_B @ sk_C))),
% 0.47/0.67      inference('sup-', [status(thm)], ['43', '46'])).
% 0.47/0.67  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.47/0.67  thf(t85_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.47/0.67  thf('49', plain,
% 0.47/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X12 @ X13)
% 0.47/0.67          | (r1_xboole_0 @ X12 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.47/0.67  thf('50', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['48', '49'])).
% 0.47/0.67  thf('51', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.47/0.67      inference('sup+', [status(thm)], ['47', '50'])).
% 0.47/0.67  thf('52', plain,
% 0.47/0.67      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.47/0.67         (~ (r1_tarski @ X15 @ X16)
% 0.47/0.67          | ~ (r1_xboole_0 @ X15 @ X17)
% 0.47/0.67          | (r1_tarski @ X15 @ (k4_xboole_0 @ X16 @ X17)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.47/0.67  thf('53', plain,
% 0.47/0.67      (![X0 : $i]:
% 0.47/0.67         ((r1_tarski @ sk_C @ (k4_xboole_0 @ X0 @ sk_B))
% 0.47/0.67          | ~ (r1_tarski @ sk_C @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.67  thf('54', plain, ((r1_tarski @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['31', '53'])).
% 0.47/0.67  thf('55', plain,
% 0.47/0.67      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.47/0.67  thf('56', plain, ((r1_tarski @ sk_C @ (k5_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('demod', [status(thm)], ['54', '55'])).
% 0.47/0.67  thf('57', plain, ($false), inference('demod', [status(thm)], ['20', '56'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
