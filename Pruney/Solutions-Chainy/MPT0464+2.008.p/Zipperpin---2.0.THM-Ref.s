%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OJ21NOAUgU

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:09 EST 2020

% Result     : Theorem 56.86s
% Output     : Refutation 56.86s
% Verified   : 
% Statistics : Number of formulae       :   53 (  77 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  422 ( 670 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('15',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k5_relat_1 @ X16 @ X15 ) @ ( k5_relat_1 @ X16 @ X14 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X2 @ X4 )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OJ21NOAUgU
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:10:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 56.86/57.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 56.86/57.11  % Solved by: fo/fo7.sh
% 56.86/57.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.86/57.11  % done 18805 iterations in 56.640s
% 56.86/57.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 56.86/57.11  % SZS output start Refutation
% 56.86/57.11  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 56.86/57.11  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 56.86/57.11  thf(sk_C_type, type, sk_C: $i).
% 56.86/57.11  thf(sk_A_type, type, sk_A: $i).
% 56.86/57.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 56.86/57.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 56.86/57.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 56.86/57.11  thf(sk_B_type, type, sk_B: $i).
% 56.86/57.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 56.86/57.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 56.86/57.11  thf(commutativity_k3_xboole_0, axiom,
% 56.86/57.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 56.86/57.11  thf('0', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 56.86/57.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 56.86/57.11  thf(t48_xboole_1, axiom,
% 56.86/57.11    (![A:$i,B:$i]:
% 56.86/57.11     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 56.86/57.11  thf('1', plain,
% 56.86/57.11      (![X7 : $i, X8 : $i]:
% 56.86/57.11         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 56.86/57.11           = (k3_xboole_0 @ X7 @ X8))),
% 56.86/57.11      inference('cnf', [status(esa)], [t48_xboole_1])).
% 56.86/57.11  thf(t36_xboole_1, axiom,
% 56.86/57.11    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 56.86/57.11  thf('2', plain,
% 56.86/57.11      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 56.86/57.11      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.86/57.11  thf('3', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 56.86/57.11      inference('sup+', [status(thm)], ['1', '2'])).
% 56.86/57.11  thf('4', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 56.86/57.11      inference('sup+', [status(thm)], ['0', '3'])).
% 56.86/57.11  thf(t3_subset, axiom,
% 56.86/57.11    (![A:$i,B:$i]:
% 56.86/57.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 56.86/57.11  thf('5', plain,
% 56.86/57.11      (![X9 : $i, X11 : $i]:
% 56.86/57.11         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 56.86/57.11      inference('cnf', [status(esa)], [t3_subset])).
% 56.86/57.11  thf('6', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]:
% 56.86/57.11         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 56.86/57.11      inference('sup-', [status(thm)], ['4', '5'])).
% 56.86/57.11  thf(cc2_relat_1, axiom,
% 56.86/57.11    (![A:$i]:
% 56.86/57.11     ( ( v1_relat_1 @ A ) =>
% 56.86/57.11       ( ![B:$i]:
% 56.86/57.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 56.86/57.11  thf('7', plain,
% 56.86/57.11      (![X12 : $i, X13 : $i]:
% 56.86/57.11         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 56.86/57.11          | (v1_relat_1 @ X12)
% 56.86/57.11          | ~ (v1_relat_1 @ X13))),
% 56.86/57.11      inference('cnf', [status(esa)], [cc2_relat_1])).
% 56.86/57.11  thf('8', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 56.86/57.11      inference('sup-', [status(thm)], ['6', '7'])).
% 56.86/57.11  thf('9', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 56.86/57.11      inference('sup+', [status(thm)], ['0', '3'])).
% 56.86/57.11  thf(t48_relat_1, axiom,
% 56.86/57.11    (![A:$i]:
% 56.86/57.11     ( ( v1_relat_1 @ A ) =>
% 56.86/57.11       ( ![B:$i]:
% 56.86/57.11         ( ( v1_relat_1 @ B ) =>
% 56.86/57.11           ( ![C:$i]:
% 56.86/57.11             ( ( v1_relat_1 @ C ) =>
% 56.86/57.11               ( ( r1_tarski @ A @ B ) =>
% 56.86/57.11                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 56.86/57.11  thf('10', plain,
% 56.86/57.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X14)
% 56.86/57.11          | ~ (r1_tarski @ X15 @ X14)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 56.86/57.11          | ~ (v1_relat_1 @ X16)
% 56.86/57.11          | ~ (v1_relat_1 @ X15))),
% 56.86/57.11      inference('cnf', [status(esa)], [t48_relat_1])).
% 56.86/57.11  thf('11', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 56.86/57.11          | ~ (v1_relat_1 @ X2)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X0))
% 56.86/57.11          | ~ (v1_relat_1 @ X0))),
% 56.86/57.11      inference('sup-', [status(thm)], ['9', '10'])).
% 56.86/57.11  thf('12', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X0)
% 56.86/57.11          | ~ (v1_relat_1 @ X0)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X0))
% 56.86/57.11          | ~ (v1_relat_1 @ X2))),
% 56.86/57.11      inference('sup-', [status(thm)], ['8', '11'])).
% 56.86/57.11  thf('13', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X2)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X0))
% 56.86/57.11          | ~ (v1_relat_1 @ X0))),
% 56.86/57.11      inference('simplify', [status(thm)], ['12'])).
% 56.86/57.11  thf('14', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 56.86/57.11      inference('sup+', [status(thm)], ['1', '2'])).
% 56.86/57.11  thf('15', plain,
% 56.86/57.11      (![X9 : $i, X11 : $i]:
% 56.86/57.11         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 56.86/57.11      inference('cnf', [status(esa)], [t3_subset])).
% 56.86/57.11  thf('16', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]:
% 56.86/57.11         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 56.86/57.11      inference('sup-', [status(thm)], ['14', '15'])).
% 56.86/57.11  thf('17', plain,
% 56.86/57.11      (![X12 : $i, X13 : $i]:
% 56.86/57.11         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 56.86/57.11          | (v1_relat_1 @ X12)
% 56.86/57.11          | ~ (v1_relat_1 @ X13))),
% 56.86/57.11      inference('cnf', [status(esa)], [cc2_relat_1])).
% 56.86/57.11  thf('18', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 56.86/57.11      inference('sup-', [status(thm)], ['16', '17'])).
% 56.86/57.11  thf('19', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 56.86/57.11      inference('sup+', [status(thm)], ['1', '2'])).
% 56.86/57.11  thf('20', plain,
% 56.86/57.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X14)
% 56.86/57.11          | ~ (r1_tarski @ X15 @ X14)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X16 @ X15) @ (k5_relat_1 @ X16 @ X14))
% 56.86/57.11          | ~ (v1_relat_1 @ X16)
% 56.86/57.11          | ~ (v1_relat_1 @ X15))),
% 56.86/57.11      inference('cnf', [status(esa)], [t48_relat_1])).
% 56.86/57.11  thf('21', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 56.86/57.11          | ~ (v1_relat_1 @ X2)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X0))
% 56.86/57.11          | ~ (v1_relat_1 @ X0))),
% 56.86/57.11      inference('sup-', [status(thm)], ['19', '20'])).
% 56.86/57.11  thf('22', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X1)
% 56.86/57.11          | ~ (v1_relat_1 @ X1)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X1))
% 56.86/57.11          | ~ (v1_relat_1 @ X2))),
% 56.86/57.11      inference('sup-', [status(thm)], ['18', '21'])).
% 56.86/57.11  thf('23', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X2)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 56.86/57.11             (k5_relat_1 @ X2 @ X1))
% 56.86/57.11          | ~ (v1_relat_1 @ X1))),
% 56.86/57.11      inference('simplify', [status(thm)], ['22'])).
% 56.86/57.11  thf(t19_xboole_1, axiom,
% 56.86/57.11    (![A:$i,B:$i,C:$i]:
% 56.86/57.11     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 56.86/57.11       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 56.86/57.11  thf('24', plain,
% 56.86/57.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 56.86/57.11         (~ (r1_tarski @ X2 @ X3)
% 56.86/57.11          | ~ (r1_tarski @ X2 @ X4)
% 56.86/57.11          | (r1_tarski @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 56.86/57.11      inference('cnf', [status(esa)], [t19_xboole_1])).
% 56.86/57.11  thf('25', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X0)
% 56.86/57.11          | ~ (v1_relat_1 @ X1)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 56.86/57.11             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 56.86/57.11          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 56.86/57.11      inference('sup-', [status(thm)], ['23', '24'])).
% 56.86/57.11  thf('26', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X0)
% 56.86/57.11          | ~ (v1_relat_1 @ X1)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 56.86/57.11             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 56.86/57.11          | ~ (v1_relat_1 @ X1)
% 56.86/57.11          | ~ (v1_relat_1 @ X2))),
% 56.86/57.11      inference('sup-', [status(thm)], ['13', '25'])).
% 56.86/57.11  thf('27', plain,
% 56.86/57.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.86/57.11         (~ (v1_relat_1 @ X2)
% 56.86/57.11          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 56.86/57.11             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 56.86/57.11          | ~ (v1_relat_1 @ X1)
% 56.86/57.11          | ~ (v1_relat_1 @ X0))),
% 56.86/57.11      inference('simplify', [status(thm)], ['26'])).
% 56.86/57.11  thf(t52_relat_1, conjecture,
% 56.86/57.11    (![A:$i]:
% 56.86/57.11     ( ( v1_relat_1 @ A ) =>
% 56.86/57.11       ( ![B:$i]:
% 56.86/57.11         ( ( v1_relat_1 @ B ) =>
% 56.86/57.11           ( ![C:$i]:
% 56.86/57.11             ( ( v1_relat_1 @ C ) =>
% 56.86/57.11               ( r1_tarski @
% 56.86/57.11                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 56.86/57.11                 ( k3_xboole_0 @
% 56.86/57.11                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 56.86/57.11  thf(zf_stmt_0, negated_conjecture,
% 56.86/57.11    (~( ![A:$i]:
% 56.86/57.11        ( ( v1_relat_1 @ A ) =>
% 56.86/57.11          ( ![B:$i]:
% 56.86/57.11            ( ( v1_relat_1 @ B ) =>
% 56.86/57.11              ( ![C:$i]:
% 56.86/57.11                ( ( v1_relat_1 @ C ) =>
% 56.86/57.11                  ( r1_tarski @
% 56.86/57.11                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 56.86/57.11                    ( k3_xboole_0 @
% 56.86/57.11                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 56.86/57.11    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 56.86/57.11  thf('28', plain,
% 56.86/57.11      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 56.86/57.11          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 56.86/57.11           (k5_relat_1 @ sk_A @ sk_C)))),
% 56.86/57.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.86/57.11  thf('29', plain,
% 56.86/57.11      ((~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 56.86/57.11      inference('sup-', [status(thm)], ['27', '28'])).
% 56.86/57.11  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 56.86/57.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.86/57.11  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 56.86/57.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.86/57.11  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 56.86/57.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.86/57.11  thf('33', plain, ($false),
% 56.86/57.11      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 56.86/57.11  
% 56.86/57.11  % SZS output end Refutation
% 56.86/57.11  
% 56.86/57.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
