%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4fPWH66dim

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   48 (  55 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  291 ( 367 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ ( k1_zfmisc_1 @ ( k3_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t211_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
       => ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) )
          = ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k6_subset_1 @ X13 @ ( k7_relat_1 @ X13 @ X15 ) )
        = ( k7_relat_1 @ X13 @ ( k6_subset_1 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t211_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k4_xboole_0 @ X13 @ ( k7_relat_1 @ X13 @ X15 ) )
        = ( k7_relat_1 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k7_relat_1 @ X0 @ ( k4_xboole_0 @ ( k1_zfmisc_1 @ ( k3_tarski @ ( k1_relat_1 @ X0 ) ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X5 @ X6 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X12 @ X10 ) @ X11 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k6_subset_1 @ X8 @ X9 )
      = ( k4_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4fPWH66dim
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 98 iterations in 0.083s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.53  thf(t100_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X7 : $i]: (r1_tarski @ X7 @ (k1_zfmisc_1 @ (k3_tarski @ X7)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.53  thf(t211_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) =>
% 0.20/0.53         ( ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) =
% 0.20/0.53           ( k7_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.53          | ((k6_subset_1 @ X13 @ (k7_relat_1 @ X13 @ X15))
% 0.20/0.53              = (k7_relat_1 @ X13 @ (k6_subset_1 @ X14 @ X15)))
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t211_relat_1])).
% 0.20/0.53  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.20/0.53          | ((k4_xboole_0 @ X13 @ (k7_relat_1 @ X13 @ X15))
% 0.20/0.53              = (k7_relat_1 @ X13 @ (k4_xboole_0 @ X14 @ X15)))
% 0.20/0.53          | ~ (v1_relat_1 @ X13))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.53              = (k7_relat_1 @ X0 @ 
% 0.20/0.53                 (k4_xboole_0 @ 
% 0.20/0.53                  (k1_zfmisc_1 @ (k3_tarski @ (k1_relat_1 @ X0))) @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '4'])).
% 0.20/0.53  thf(t79_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X5 @ X6) @ X6)),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf(t216_relat_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.53           ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ C ) =>
% 0.20/0.53          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.53              ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.20/0.53  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t63_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.53          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.53          | (r1_xboole_0 @ X2 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf(t207_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r1_xboole_0 @ A @ B ) =>
% 0.20/0.53         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ X10 @ X11)
% 0.20/0.53          | ~ (v1_relat_1 @ X12)
% 0.20/0.53          | ((k7_relat_1 @ (k7_relat_1 @ X12 @ X10) @ X11) = (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k7_relat_1 @ (k7_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.53            = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.53            = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['5', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.53              = (k1_xboole_0)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.20/0.53         != (k1_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]: ((k6_subset_1 @ X8 @ X9) = (k4_xboole_0 @ X8 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.20/0.53         != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.53  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
