%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DRpE304ekG

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:16 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   69 (  95 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  555 (1011 expanded)
%              Number of equality atoms :   40 (  64 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) )
      | ( ( k4_subset_1 @ X19 @ X18 @ X20 )
        = ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k3_subset_1 @ sk_A @ ( k7_subset_1 @ sk_A @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_subset_1 @ X17 @ ( k3_subset_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('19',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['16','27'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
    = ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ( k2_xboole_0 @ sk_C @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k4_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['8','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DRpE304ekG
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 2.43/2.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.43/2.67  % Solved by: fo/fo7.sh
% 2.43/2.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.43/2.67  % done 686 iterations in 2.180s
% 2.43/2.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.43/2.67  % SZS output start Refutation
% 2.43/2.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.43/2.67  thf(sk_A_type, type, sk_A: $i).
% 2.43/2.67  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.43/2.67  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.43/2.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.43/2.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.43/2.67  thf(sk_B_type, type, sk_B: $i).
% 2.43/2.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.43/2.67  thf(sk_C_type, type, sk_C: $i).
% 2.43/2.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.43/2.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.43/2.67  thf(t33_subset_1, conjecture,
% 2.43/2.67    (![A:$i,B:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( ![C:$i]:
% 2.43/2.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.43/2.67             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.43/2.67  thf(zf_stmt_0, negated_conjecture,
% 2.43/2.67    (~( ![A:$i,B:$i]:
% 2.43/2.67        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67          ( ![C:$i]:
% 2.43/2.67            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67              ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.43/2.67                ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ) )),
% 2.43/2.67    inference('cnf.neg', [status(esa)], [t33_subset_1])).
% 2.43/2.67  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf(dt_k3_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.43/2.67  thf('2', plain,
% 2.43/2.67      (![X11 : $i, X12 : $i]:
% 2.43/2.67         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 2.43/2.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.43/2.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.43/2.67  thf('3', plain,
% 2.43/2.67      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('sup-', [status(thm)], ['1', '2'])).
% 2.43/2.67  thf(redefinition_k4_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i,C:$i]:
% 2.43/2.67     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.43/2.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.43/2.67       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.43/2.67  thf('4', plain,
% 2.43/2.67      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.43/2.67         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.43/2.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19))
% 2.43/2.67          | ((k4_subset_1 @ X19 @ X18 @ X20) = (k2_xboole_0 @ X18 @ X20)))),
% 2.43/2.67      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.43/2.67  thf('5', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 2.43/2.67            = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 2.43/2.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 2.43/2.67      inference('sup-', [status(thm)], ['3', '4'])).
% 2.43/2.67  thf('6', plain,
% 2.43/2.67      (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 2.43/2.67         = (k2_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 2.43/2.67      inference('sup-', [status(thm)], ['0', '5'])).
% 2.43/2.67  thf(commutativity_k2_xboole_0, axiom,
% 2.43/2.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.43/2.67  thf('7', plain,
% 2.43/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.43/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.43/2.67  thf('8', plain,
% 2.43/2.67      (((k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 2.43/2.67         = (k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B)))),
% 2.43/2.67      inference('demod', [status(thm)], ['6', '7'])).
% 2.43/2.67  thf('9', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k7_subset_1 @ sk_A @ sk_B @ sk_C))
% 2.43/2.67         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf(redefinition_k7_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i,C:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.43/2.67  thf('11', plain,
% 2.43/2.67      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.43/2.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 2.43/2.67          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 2.43/2.67      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.43/2.67  thf('12', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 2.43/2.67      inference('sup-', [status(thm)], ['10', '11'])).
% 2.43/2.67  thf('13', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.43/2.67         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 2.43/2.67      inference('demod', [status(thm)], ['9', '12'])).
% 2.43/2.67  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf(involutiveness_k3_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.43/2.67  thf('15', plain,
% 2.43/2.67      (![X16 : $i, X17 : $i]:
% 2.43/2.67         (((k3_subset_1 @ X17 @ (k3_subset_1 @ X17 @ X16)) = (X16))
% 2.43/2.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.43/2.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.43/2.67  thf('16', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 2.43/2.67      inference('sup-', [status(thm)], ['14', '15'])).
% 2.43/2.67  thf('17', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf('18', plain,
% 2.43/2.67      (![X11 : $i, X12 : $i]:
% 2.43/2.67         ((m1_subset_1 @ (k3_subset_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 2.43/2.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.43/2.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.43/2.67  thf('19', plain,
% 2.43/2.67      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('sup-', [status(thm)], ['17', '18'])).
% 2.43/2.67  thf(d5_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.43/2.67  thf('20', plain,
% 2.43/2.67      (![X9 : $i, X10 : $i]:
% 2.43/2.67         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 2.43/2.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 2.43/2.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.43/2.67  thf('21', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 2.43/2.67         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 2.43/2.67      inference('sup-', [status(thm)], ['19', '20'])).
% 2.43/2.67  thf('22', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf('23', plain,
% 2.43/2.67      (![X9 : $i, X10 : $i]:
% 2.43/2.67         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 2.43/2.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 2.43/2.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.43/2.67  thf('24', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 2.43/2.67      inference('sup-', [status(thm)], ['22', '23'])).
% 2.43/2.67  thf(t48_xboole_1, axiom,
% 2.43/2.67    (![A:$i,B:$i]:
% 2.43/2.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.43/2.67  thf('25', plain,
% 2.43/2.67      (![X2 : $i, X3 : $i]:
% 2.43/2.67         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 2.43/2.67           = (k3_xboole_0 @ X2 @ X3))),
% 2.43/2.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.43/2.67  thf('26', plain,
% 2.43/2.67      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 2.43/2.67         = (k3_xboole_0 @ sk_A @ sk_C))),
% 2.43/2.67      inference('sup+', [status(thm)], ['24', '25'])).
% 2.43/2.67  thf('27', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 2.43/2.67         = (k3_xboole_0 @ sk_A @ sk_C))),
% 2.43/2.67      inference('sup+', [status(thm)], ['21', '26'])).
% 2.43/2.67  thf('28', plain, (((sk_C) = (k3_xboole_0 @ sk_A @ sk_C))),
% 2.43/2.67      inference('sup+', [status(thm)], ['16', '27'])).
% 2.43/2.67  thf(t52_xboole_1, axiom,
% 2.43/2.67    (![A:$i,B:$i,C:$i]:
% 2.43/2.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.43/2.67       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.43/2.67  thf('29', plain,
% 2.43/2.67      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.43/2.67         ((k4_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 2.43/2.67           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X6)))),
% 2.43/2.67      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.43/2.67  thf('30', plain,
% 2.43/2.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.43/2.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.43/2.67  thf('31', plain,
% 2.43/2.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.67         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X2 @ X1))
% 2.43/2.67           = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.43/2.67      inference('sup+', [status(thm)], ['29', '30'])).
% 2.43/2.67  thf('32', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         ((k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))
% 2.43/2.67           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C)))),
% 2.43/2.67      inference('sup+', [status(thm)], ['28', '31'])).
% 2.43/2.67  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf(dt_k7_subset_1, axiom,
% 2.43/2.67    (![A:$i,B:$i,C:$i]:
% 2.43/2.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.43/2.67       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.43/2.67  thf('34', plain,
% 2.43/2.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.43/2.67         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.43/2.67          | (m1_subset_1 @ (k7_subset_1 @ X14 @ X13 @ X15) @ 
% 2.43/2.67             (k1_zfmisc_1 @ X14)))),
% 2.43/2.67      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 2.43/2.67  thf('35', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         (m1_subset_1 @ (k7_subset_1 @ sk_A @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('sup-', [status(thm)], ['33', '34'])).
% 2.43/2.67  thf('36', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 2.43/2.67      inference('sup-', [status(thm)], ['10', '11'])).
% 2.43/2.67  thf('37', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('demod', [status(thm)], ['35', '36'])).
% 2.43/2.67  thf('38', plain,
% 2.43/2.67      (![X9 : $i, X10 : $i]:
% 2.43/2.67         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 2.43/2.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 2.43/2.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.43/2.67  thf('39', plain,
% 2.43/2.67      (![X0 : $i]:
% 2.43/2.67         ((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 2.43/2.67           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 2.43/2.67      inference('sup-', [status(thm)], ['37', '38'])).
% 2.43/2.67  thf('40', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.43/2.67         = (k2_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 2.43/2.67      inference('sup+', [status(thm)], ['32', '39'])).
% 2.43/2.67  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.43/2.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.67  thf('42', plain,
% 2.43/2.67      (![X9 : $i, X10 : $i]:
% 2.43/2.67         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 2.43/2.67          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 2.43/2.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.43/2.67  thf('43', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.43/2.67      inference('sup-', [status(thm)], ['41', '42'])).
% 2.43/2.67  thf('44', plain,
% 2.43/2.67      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 2.43/2.67         = (k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B)))),
% 2.43/2.67      inference('demod', [status(thm)], ['40', '43'])).
% 2.43/2.67  thf('45', plain,
% 2.43/2.67      (((k2_xboole_0 @ sk_C @ (k3_subset_1 @ sk_A @ sk_B))
% 2.43/2.67         != (k4_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 2.43/2.67      inference('demod', [status(thm)], ['13', '44'])).
% 2.43/2.67  thf('46', plain, ($false),
% 2.43/2.67      inference('simplify_reflect-', [status(thm)], ['8', '45'])).
% 2.43/2.67  
% 2.43/2.67  % SZS output end Refutation
% 2.43/2.67  
% 2.53/2.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
