%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.53DpSwMmwZ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 133 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :  480 (1362 expanded)
%              Number of equality atoms :   30 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16','17','20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X10 @ X11 )
        = ( k4_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['8','34','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.53DpSwMmwZ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 124 iterations in 0.129s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(t41_subset_1, conjecture,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ![C:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58           ( r1_tarski @
% 0.20/0.58             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.20/0.58             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i]:
% 0.20/0.58        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58          ( ![C:$i]:
% 0.20/0.58            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58              ( r1_tarski @
% 0.20/0.58                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.20/0.58                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (~ (r1_tarski @ 
% 0.20/0.58          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.58          (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.58       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.20/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.20/0.58          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.58  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.20/0.58          (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '7'])).
% 0.20/0.58  thf('9', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(dt_k4_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.58       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.20/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.20/0.58          | (m1_subset_1 @ (k4_subset_1 @ X13 @ X12 @ X14) @ 
% 0.20/0.58             (k1_zfmisc_1 @ X13)))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.20/0.58           (k1_zfmisc_1 @ sk_A))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '12'])).
% 0.20/0.58  thf(d5_subset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.58       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i]:
% 0.20/0.58         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.20/0.58         = (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('17', plain,
% 0.20/0.58      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.58  thf(t41_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.58       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('20', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.20/0.58           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('22', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i]:
% 0.20/0.58         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.20/0.58         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.58      inference('demod', [status(thm)], ['15', '16', '17', '20', '23'])).
% 0.20/0.58  thf('25', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('26', plain,
% 0.20/0.58      (![X10 : $i, X11 : $i]:
% 0.20/0.58         (((k3_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))
% 0.20/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.58  thf('27', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.58  thf('28', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.20/0.58           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 0.20/0.58           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 0.20/0.58           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 0.20/0.58           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['28', '31'])).
% 0.20/0.58  thf('33', plain,
% 0.20/0.58      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.20/0.58         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['27', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.20/0.58         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['24', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C)
% 0.20/0.58         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['27', '32'])).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.58  thf(t7_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X8 : $i, X9 : $i]: (r1_tarski @ X8 @ (k2_xboole_0 @ X8 @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.58      inference('sup+', [status(thm)], ['36', '37'])).
% 0.20/0.58  thf(t43_xboole_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.58       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.58         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.20/0.58          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('41', plain,
% 0.20/0.58      ((r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_B) @ 
% 0.20/0.58        (k3_subset_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['35', '40'])).
% 0.20/0.58  thf('42', plain, ($false),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '34', '41'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
