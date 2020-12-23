%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOx3lFje5u

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 155 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  506 (1790 expanded)
%              Number of equality atoms :   37 ( 140 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X18 @ ( k7_setfam_1 @ X18 @ X17 ) )
        = ( k3_subset_1 @ X18 @ ( k5_setfam_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('5',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_setfam_1 @ X16 @ ( k7_setfam_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('8',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
      = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','17'])).

thf('19',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','17'])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ( r2_hidden @ ( k3_subset_1 @ X8 @ ( sk_D @ X7 @ X9 @ X8 ) ) @ X9 )
      | ( X7
        = ( k7_setfam_1 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('24',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf('25',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( k1_xboole_0 = sk_B ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('35',plain,(
    $false ),
    inference('sup-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BOx3lFje5u
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 113 iterations in 0.052s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.51  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(t12_tops_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.51           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.51              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k7_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @
% 0.20/0.51         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t11_tops_2, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.20/0.51           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (((X17) = (k1_xboole_0))
% 0.20/0.51          | ((k6_setfam_1 @ X18 @ (k7_setfam_1 @ X18 @ X17))
% 0.20/0.51              = (k3_subset_1 @ X18 @ (k5_setfam_1 @ X18 @ X17)))
% 0.20/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((((k6_setfam_1 @ sk_A @ 
% 0.20/0.51          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.51          = (k3_subset_1 @ sk_A @ 
% 0.20/0.51             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.20/0.51        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(involutiveness_k7_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (((k7_setfam_1 @ X16 @ (k7_setfam_1 @ X16 @ X15)) = (X15))
% 0.20/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.20/0.51      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((((k6_setfam_1 @ sk_A @ sk_B)
% 0.20/0.51          = (k3_subset_1 @ sk_A @ 
% 0.20/0.51             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.20/0.51        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(dt_k5_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k5_setfam_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11))
% 0.20/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.20/0.51        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ 
% 0.20/0.51         (k3_subset_1 @ sk_A @ 
% 0.20/0.51          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.20/0.51         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.20/0.51          = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.20/0.51        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.51         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '17'])).
% 0.20/0.51  thf(d8_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.51           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.51             ( ![D:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8)))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.20/0.51          | (r2_hidden @ (k3_subset_1 @ X8 @ (sk_D @ X7 @ X9 @ X8)) @ X9)
% 0.20/0.51          | ((X7) = (k7_setfam_1 @ X8 @ X9))
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.51          | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ X0))
% 0.20/0.51          | (r2_hidden @ 
% 0.20/0.51             (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ X0 @ sk_A)) @ X0)
% 0.20/0.51          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.51           k1_xboole_0)
% 0.20/0.51        | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('24', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('25', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.51           k1_xboole_0)
% 0.20/0.51        | ((k1_xboole_0) = (sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '25'])).
% 0.20/0.51  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.20/0.51        | (r2_hidden @ 
% 0.20/0.51           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.51           k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf(t113_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.20/0.51  thf(t152_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.51  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((r2_hidden @ 
% 0.20/0.51        (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.20/0.51        k1_xboole_0)),
% 0.20/0.51      inference('clc', [status(thm)], ['28', '32'])).
% 0.20/0.51  thf('34', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.51  thf('35', plain, ($false), inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
