%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9zoz4RTKJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:53 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 136 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  542 (1499 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k4_subset_1 @ X14 @ X13 @ X15 )
        = ( k2_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('19',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X17 @ X16 ) @ X18 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X17 @ X18 ) @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('32',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k2_xboole_0 @ sk_C @ sk_B ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C @ sk_B ) )
    | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('42',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_B ) ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','37','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['20','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9zoz4RTKJ
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:04:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 444 iterations in 0.286s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.53/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.74  thf(t41_subset_1, conjecture,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ![C:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74           ( r1_tarski @
% 0.53/0.74             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.53/0.74             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i,B:$i]:
% 0.53/0.74        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74          ( ![C:$i]:
% 0.53/0.74            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74              ( r1_tarski @
% 0.53/0.74                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 0.53/0.74                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 0.53/0.74  thf('0', plain,
% 0.53/0.74      (~ (r1_tarski @ 
% 0.53/0.74          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.53/0.74          (k3_subset_1 @ sk_A @ sk_B))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(d5_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.53/0.74          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (~ (r1_tarski @ 
% 0.53/0.74          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.53/0.74          (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.53/0.74  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_k4_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.74       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.53/0.74          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9))
% 0.53/0.74          | (m1_subset_1 @ (k4_subset_1 @ X9 @ X8 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.53/0.74  thf('8', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ X0) @ 
% 0.53/0.74           (k1_zfmisc_1 @ sk_A))
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.53/0.74  thf('9', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '8'])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.53/0.74          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.53/0.74  thf('11', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.53/0.74         = (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('12', plain,
% 0.53/0.74      (~ (r1_tarski @ 
% 0.53/0.74          (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ 
% 0.53/0.74          (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['4', '11'])).
% 0.53/0.74  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(redefinition_k4_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.53/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.53/0.74       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.53/0.74  thf('15', plain,
% 0.53/0.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.53/0.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14))
% 0.53/0.74          | ((k4_subset_1 @ X14 @ X13 @ X15) = (k2_xboole_0 @ X13 @ X15)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.53/0.74  thf('16', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.53/0.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.74  thf('17', plain,
% 0.53/0.74      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.53/0.74      inference('sup-', [status(thm)], ['13', '16'])).
% 0.53/0.74  thf(commutativity_k2_xboole_0, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.53/0.74  thf('18', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.53/0.74  thf('19', plain,
% 0.53/0.74      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (~ (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.53/0.74          (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['12', '19'])).
% 0.53/0.74  thf('21', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(involutiveness_k3_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X11 : $i, X12 : $i]:
% 0.53/0.74         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.53/0.74          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.53/0.74      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '22'])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_subset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['5', '8'])).
% 0.53/0.74  thf(t36_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ![C:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.53/0.74             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.53/0.74          | (r1_tarski @ (k3_subset_1 @ X17 @ X16) @ X18)
% 0.53/0.74          | ~ (r1_tarski @ (k3_subset_1 @ X17 @ X18) @ X16)
% 0.53/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.53/0.74      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.74          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.53/0.74               (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.53/0.74          | (r1_tarski @ 
% 0.53/0.74             (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.53/0.74         = (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.74          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.53/0.74               (k4_subset_1 @ sk_A @ sk_B @ sk_C))
% 0.53/0.74          | (r1_tarski @ 
% 0.53/0.74             (k4_xboole_0 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C)) @ X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['28', '29'])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (((k4_subset_1 @ sk_A @ sk_B @ sk_C) = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['17', '18'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.53/0.74          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.53/0.74               (k2_xboole_0 @ sk_C @ sk_B))
% 0.53/0.74          | (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.53/0.74             X0))),
% 0.53/0.74      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.53/0.74        | (r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.53/0.74           (k4_xboole_0 @ sk_A @ sk_B))
% 0.53/0.74        | ~ (m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['25', '33'])).
% 0.53/0.74  thf('35', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.53/0.74  thf(t7_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.53/0.74  thf('36', plain,
% 0.53/0.74      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.53/0.74      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['35', '36'])).
% 0.53/0.74  thf('38', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(dt_k3_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X6 : $i, X7 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['38', '39'])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      ((m1_subset_1 @ (k4_xboole_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['40', '41'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      ((r1_tarski @ (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_B)) @ 
% 0.53/0.74        (k4_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.74      inference('demod', [status(thm)], ['34', '37', '42'])).
% 0.53/0.74  thf('44', plain, ($false), inference('demod', [status(thm)], ['20', '43'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
