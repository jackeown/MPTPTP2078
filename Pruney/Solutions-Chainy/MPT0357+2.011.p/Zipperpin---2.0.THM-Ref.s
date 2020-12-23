%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SoXq2EyNmg

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 162 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  572 (1530 expanded)
%              Number of equality atoms :   32 (  88 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k6_subset_1 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('13',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k6_subset_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k6_subset_1 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( r1_tarski @ X10 @ ( k3_subset_1 @ X11 @ X12 ) )
      | ~ ( r1_tarski @ X12 @ ( k3_subset_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) @ ( k3_subset_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X2 ) ) @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k6_subset_1 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C ) ) ) @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['16','17','20'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_C )
      | ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('47',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['6','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SoXq2EyNmg
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:11:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 56 iterations in 0.028s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t36_subset_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.21/0.47             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47              ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.21/0.47                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t36_subset_1])).
% 0.21/0.47  thf('0', plain, (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d5_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.47  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X2 @ X3) = (k6_subset_1 @ X2 @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf('6', plain, (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['0', '5'])).
% 0.21/0.47  thf('7', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('13', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_C) = (k6_subset_1 @ sk_A @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.47  thf(dt_k6_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X2 @ X3) = (k6_subset_1 @ X2 @ X3))
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (((k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47           = (k6_subset_1 @ X0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47           = (k6_subset_1 @ X0 @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k6_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.21/0.47  thf(t35_subset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.47           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.21/0.47             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.21/0.47          | (r1_tarski @ X10 @ (k3_subset_1 @ X11 @ X12))
% 0.21/0.47          | ~ (r1_tarski @ X12 @ (k3_subset_1 @ X11 @ X10))
% 0.21/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.21/0.47          | ~ (r1_tarski @ X2 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X2)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.21/0.47          | ~ (r1_tarski @ X2 @ (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47          | (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_subset_1 @ X0 @ X2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r1_tarski @ X2 @ (k6_subset_1 @ X1 @ X0))
% 0.21/0.47          | (r1_tarski @ (k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0)) @ 
% 0.21/0.47             (k3_subset_1 @ X1 @ X2))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['28', '33'])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_tarski @ (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2)) @ 
% 0.21/0.47           (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47          | ~ (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '34'])).
% 0.21/0.47  thf('36', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_tarski @ (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X2)) @ 
% 0.21/0.47           (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.21/0.47          | ~ (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ (k6_subset_1 @ X0 @ X2)))),
% 0.21/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_C)
% 0.21/0.47          | (r1_tarski @ 
% 0.21/0.47             (k6_subset_1 @ sk_A @ 
% 0.21/0.47              (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C))) @ 
% 0.21/0.47             (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (((k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17', '20'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ sk_C)
% 0.21/0.47          | (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47             (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ X0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ 
% 0.21/0.47        (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '40'])).
% 0.21/0.47  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.47      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('46', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.47  thf('47', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ sk_B) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.47  thf('48', plain,
% 0.21/0.47      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['44', '47'])).
% 0.21/0.47  thf('49', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.21/0.47           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('50', plain,
% 0.21/0.47      (((k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain, ((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['41', '50'])).
% 0.21/0.47  thf('52', plain, ($false), inference('demod', [status(thm)], ['6', '51'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
