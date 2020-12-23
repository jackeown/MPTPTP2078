%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BhBXxv5SmY

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  414 ( 514 expanded)
%              Number of equality atoms :   43 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t201_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( k7_relat_1 @ B @ A )
              = ( k7_relat_1 @ C @ A ) )
           => ( ( k9_relat_1 @ B @ A )
              = ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k9_relat_1 @ X10 @ X9 )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ( ( k7_relat_1 @ X10 @ X9 )
       != ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t201_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ sk_B )
       != ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ sk_B )
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ sk_B )
       != ( k6_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ sk_B )
        = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_B )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('33',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('36',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','34','35'])).

thf('37',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BhBXxv5SmY
% 0.12/0.37  % Computer   : n005.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 15:24:18 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 29 iterations in 0.016s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(t94_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.46  thf('0', plain,
% 0.22/0.46      (![X15 : $i, X16 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.22/0.46          | ~ (v1_relat_1 @ X16))),
% 0.22/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.46  thf(d10_xboole_0, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.46  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.46      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.46  thf(t79_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.46         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.22/0.46          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 0.22/0.46          | ~ (v1_relat_1 @ X13))),
% 0.22/0.46      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (~ (v1_relat_1 @ X0)
% 0.22/0.46          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))) = (X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.22/0.46            = (k6_relat_1 @ X0))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['0', '4'])).
% 0.22/0.46  thf(t71_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.46  thf('6', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf('7', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.46  thf('8', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('9', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      (![X15 : $i, X16 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 0.22/0.46          | ~ (v1_relat_1 @ X16))),
% 0.22/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.46  thf(t162_funct_1, conjecture,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i]:
% 0.22/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.46          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.22/0.46  thf('12', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t3_subset, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.46  thf('13', plain,
% 0.22/0.46      (![X3 : $i, X4 : $i]:
% 0.22/0.46         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.46  thf('14', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.22/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.46  thf('15', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      (![X13 : $i, X14 : $i]:
% 0.22/0.46         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.22/0.46          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 0.22/0.46          | ~ (v1_relat_1 @ X13))),
% 0.22/0.46      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.22/0.46  thf('17', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.22/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.22/0.46              = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.46  thf('18', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (![X0 : $i, X1 : $i]:
% 0.22/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.22/0.46              = (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.46  thf('20', plain,
% 0.22/0.46      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.22/0.46         = (k6_relat_1 @ sk_B))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '19'])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))
% 0.22/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['11', '20'])).
% 0.22/0.46  thf('22', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('23', plain,
% 0.22/0.46      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))),
% 0.22/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.46  thf(t201_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ B ) =>
% 0.22/0.46       ( ![C:$i]:
% 0.22/0.46         ( ( v1_relat_1 @ C ) =>
% 0.22/0.46           ( ( ( k7_relat_1 @ B @ A ) = ( k7_relat_1 @ C @ A ) ) =>
% 0.22/0.46             ( ( k9_relat_1 @ B @ A ) = ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.46  thf('24', plain,
% 0.22/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.46         (~ (v1_relat_1 @ X8)
% 0.22/0.46          | ((k9_relat_1 @ X10 @ X9) = (k9_relat_1 @ X8 @ X9))
% 0.22/0.46          | ((k7_relat_1 @ X10 @ X9) != (k7_relat_1 @ X8 @ X9))
% 0.22/0.46          | ~ (v1_relat_1 @ X10))),
% 0.22/0.46      inference('cnf', [status(esa)], [t201_relat_1])).
% 0.22/0.46  thf('25', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X0 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.22/0.46          | ~ (v1_relat_1 @ X0)
% 0.22/0.46          | ((k9_relat_1 @ X0 @ sk_B)
% 0.22/0.46              = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.46  thf('26', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('27', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k7_relat_1 @ X0 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.22/0.46          | ~ (v1_relat_1 @ X0)
% 0.22/0.46          | ((k9_relat_1 @ X0 @ sk_B)
% 0.22/0.46              = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.46  thf('28', plain,
% 0.22/0.46      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.22/0.46        | ((k9_relat_1 @ (k6_relat_1 @ sk_B) @ sk_B)
% 0.22/0.46            = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.22/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 0.22/0.46      inference('sup-', [status(thm)], ['10', '27'])).
% 0.22/0.46  thf('29', plain, (![X11 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf(t146_relat_1, axiom,
% 0.22/0.46    (![A:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ A ) =>
% 0.22/0.46       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.22/0.46  thf('30', plain,
% 0.22/0.46      (![X7 : $i]:
% 0.22/0.46         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.22/0.46          | ~ (v1_relat_1 @ X7))),
% 0.22/0.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.22/0.46  thf('31', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.22/0.46            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.22/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.46      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.46  thf('32', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.22/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.46  thf('33', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('34', plain,
% 0.22/0.46      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.22/0.46      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.22/0.46  thf('35', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.22/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.46  thf('36', plain,
% 0.22/0.46      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.22/0.46        | ((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.22/0.46      inference('demod', [status(thm)], ['28', '34', '35'])).
% 0.22/0.46  thf('37', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.22/0.46      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.46  thf('38', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('39', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
