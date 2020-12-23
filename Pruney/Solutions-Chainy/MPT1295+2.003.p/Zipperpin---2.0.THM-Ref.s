%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uz9A26lqYE

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 (  84 expanded)
%              Number of leaves         :   27 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  419 ( 635 expanded)
%              Number of equality atoms :   41 (  65 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X21 @ ( k2_subset_1 @ X21 ) @ ( k5_setfam_1 @ X21 @ X20 ) )
        = ( k6_setfam_1 @ X21 @ ( k7_setfam_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t47_setfam_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = ( k3_subset_1 @ X14 @ ( k1_subset_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( ( k7_subset_1 @ X21 @ X21 @ ( k5_setfam_1 @ X21 @ X20 ) )
        = ( k6_setfam_1 @ X21 @ ( k7_setfam_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['1','14'])).

thf('16',plain,
    ( ( ( k7_subset_1 @ sk_A @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k7_subset_1 @ sk_A @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['7','12'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('30',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k4_xboole_0 @ sk_A @ ( k5_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uz9A26lqYE
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:08:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 122 iterations in 0.058s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.52  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(t11_tops_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.52           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52            ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.52              ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t11_tops_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t47_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52         ( ( k7_subset_1 @ A @ ( k2_subset_1 @ A ) @ ( k5_setfam_1 @ A @ B ) ) =
% 0.22/0.52           ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (((X20) = (k1_xboole_0))
% 0.22/0.52          | ((k7_subset_1 @ X21 @ (k2_subset_1 @ X21) @ 
% 0.22/0.52              (k5_setfam_1 @ X21 @ X20))
% 0.22/0.52              = (k6_setfam_1 @ X21 @ (k7_setfam_1 @ X21 @ X20)))
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t47_setfam_1])).
% 0.22/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('2', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.52  thf(t22_subset_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         ((k2_subset_1 @ X14) = (k3_subset_1 @ X14 @ (k1_subset_1 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]: ((k2_subset_1 @ X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(t2_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.52  thf(t100_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.52           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf(t5_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('11', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.52  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '12'])).
% 0.22/0.52  thf('14', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['4', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (((X20) = (k1_xboole_0))
% 0.22/0.52          | ((k7_subset_1 @ X21 @ X21 @ (k5_setfam_1 @ X21 @ X20))
% 0.22/0.52              = (k6_setfam_1 @ X21 @ (k7_setfam_1 @ X21 @ X20)))
% 0.22/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((((k7_subset_1 @ sk_A @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52          = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.22/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '15'])).
% 0.22/0.52  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((k7_subset_1 @ sk_A @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52         = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(dt_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.22/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '12'])).
% 0.22/0.52  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.22/0.52          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52         = (k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52         != (k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k5_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k5_setfam_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52         = (k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((k6_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.22/0.52         != (k4_xboole_0 @ sk_A @ (k5_setfam_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '32'])).
% 0.22/0.52  thf('34', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['26', '33'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
