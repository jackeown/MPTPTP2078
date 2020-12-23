%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iFlhNLUsI

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:07 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   56 (  74 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  385 ( 750 expanded)
%              Number of equality atoms :   32 (  49 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( r1_xboole_0 @ B @ C )
              & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
           => ( B
              = ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( r1_xboole_0 @ B @ C )
                & ( r1_xboole_0 @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) )
             => ( B
                = ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X12 @ X13 ) @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_subset_1 @ X14 @ X15 )
        = ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( sk_C
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['5','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['2','32'])).

thf('34',plain,(
    sk_B
 != ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6iFlhNLUsI
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.66  % Solved by: fo/fo7.sh
% 0.48/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.66  % done 690 iterations in 0.210s
% 0.48/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.66  % SZS output start Refutation
% 0.48/0.66  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.48/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.66  thf(t46_subset_1, conjecture,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( ![C:$i]:
% 0.48/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66           ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.48/0.66               ( r1_xboole_0 @
% 0.48/0.66                 ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.48/0.66             ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.48/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.66    (~( ![A:$i,B:$i]:
% 0.48/0.66        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66          ( ![C:$i]:
% 0.48/0.66            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66              ( ( ( r1_xboole_0 @ B @ C ) & 
% 0.48/0.66                  ( r1_xboole_0 @
% 0.48/0.66                    ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.48/0.66                ( ( B ) = ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.48/0.66    inference('cnf.neg', [status(esa)], [t46_subset_1])).
% 0.48/0.66  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d5_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.48/0.66  thf('1', plain,
% 0.48/0.66      (![X14 : $i, X15 : $i]:
% 0.48/0.66         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.48/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.48/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.66  thf('2', plain,
% 0.48/0.66      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.48/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.48/0.66  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(t88_xboole_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( r1_xboole_0 @ A @ B ) =>
% 0.48/0.66       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.48/0.66  thf('4', plain,
% 0.48/0.66      (![X12 : $i, X13 : $i]:
% 0.48/0.66         (((k4_xboole_0 @ (k2_xboole_0 @ X12 @ X13) @ X13) = (X12))
% 0.48/0.66          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.48/0.66      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.48/0.66  thf('5', plain,
% 0.48/0.66      (((k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ sk_C) = (sk_B))),
% 0.48/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.48/0.66  thf('6', plain,
% 0.48/0.66      ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(d7_xboole_0, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.48/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.48/0.66  thf('7', plain,
% 0.48/0.66      (![X0 : $i, X1 : $i]:
% 0.48/0.66         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.48/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.48/0.66  thf('8', plain,
% 0.48/0.66      (((k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.48/0.66         (k3_subset_1 @ sk_A @ sk_C)) = (k1_xboole_0))),
% 0.48/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.48/0.66  thf('9', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(dt_k3_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.48/0.66  thf('10', plain,
% 0.48/0.66      (![X16 : $i, X17 : $i]:
% 0.48/0.66         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.48/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.48/0.66      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.48/0.66  thf('11', plain,
% 0.48/0.66      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.48/0.66  thf('12', plain,
% 0.48/0.66      (![X14 : $i, X15 : $i]:
% 0.48/0.66         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.48/0.66          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.48/0.66      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.66  thf('13', plain,
% 0.48/0.66      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 0.48/0.66         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.48/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.48/0.66  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.66  thf(involutiveness_k3_subset_1, axiom,
% 0.48/0.66    (![A:$i,B:$i]:
% 0.48/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.66       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.48/0.66  thf('15', plain,
% 0.48/0.66      (![X18 : $i, X19 : $i]:
% 0.48/0.66         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.48/0.66          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.48/0.66      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.48/0.66  thf('16', plain,
% 0.48/0.66      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.48/0.67      inference('sup-', [status(thm)], ['14', '15'])).
% 0.48/0.67  thf('17', plain,
% 0.48/0.67      (((sk_B) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.48/0.67      inference('demod', [status(thm)], ['13', '16'])).
% 0.48/0.67  thf(t54_xboole_1, axiom,
% 0.48/0.67    (![A:$i,B:$i,C:$i]:
% 0.48/0.67     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.48/0.67       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.48/0.67  thf('18', plain,
% 0.48/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.48/0.67           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X6 @ X8)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t54_xboole_1])).
% 0.48/0.67  thf('19', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         ((k4_xboole_0 @ sk_A @ 
% 0.48/0.67           (k3_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0))
% 0.48/0.67           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.48/0.67      inference('sup+', [status(thm)], ['17', '18'])).
% 0.48/0.67  thf('20', plain,
% 0.48/0.67      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.48/0.67         = (k2_xboole_0 @ sk_B @ 
% 0.48/0.67            (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))))),
% 0.48/0.67      inference('sup+', [status(thm)], ['8', '19'])).
% 0.48/0.67  thf(t3_boole, axiom,
% 0.48/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.67  thf('21', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.48/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.48/0.67  thf('22', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('23', plain,
% 0.48/0.67      (![X16 : $i, X17 : $i]:
% 0.48/0.67         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.48/0.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.48/0.67      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.48/0.67  thf('24', plain,
% 0.48/0.67      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.48/0.67  thf('25', plain,
% 0.48/0.67      (![X14 : $i, X15 : $i]:
% 0.48/0.67         (((k3_subset_1 @ X14 @ X15) = (k4_xboole_0 @ X14 @ X15))
% 0.48/0.67          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.48/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.48/0.67  thf('26', plain,
% 0.48/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C))
% 0.48/0.67         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['24', '25'])).
% 0.48/0.67  thf('27', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('28', plain,
% 0.48/0.67      (![X18 : $i, X19 : $i]:
% 0.48/0.67         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.48/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.48/0.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.48/0.67  thf('29', plain,
% 0.48/0.67      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)) = (sk_C))),
% 0.48/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.48/0.67  thf('30', plain,
% 0.48/0.67      (((sk_C) = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C)))),
% 0.48/0.67      inference('demod', [status(thm)], ['26', '29'])).
% 0.48/0.67  thf('31', plain, (((sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.48/0.67      inference('demod', [status(thm)], ['20', '21', '30'])).
% 0.48/0.67  thf('32', plain, (((k4_xboole_0 @ sk_A @ sk_C) = (sk_B))),
% 0.48/0.67      inference('demod', [status(thm)], ['5', '31'])).
% 0.48/0.67  thf('33', plain, (((k3_subset_1 @ sk_A @ sk_C) = (sk_B))),
% 0.48/0.67      inference('sup+', [status(thm)], ['2', '32'])).
% 0.48/0.67  thf('34', plain, (((sk_B) != (k3_subset_1 @ sk_A @ sk_C))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('35', plain, ($false),
% 0.48/0.67      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.48/0.67  
% 0.48/0.67  % SZS output end Refutation
% 0.48/0.67  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
