%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XWMQDDustV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  60 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 348 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
       != ( k1_wellord2 @ X11 ) )
      | ( ( k3_relat_1 @ X12 )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X11 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
        = X11 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X11: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X10 )
      | ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XWMQDDustV
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 39 iterations in 0.024s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(t33_wellord2, conjecture,
% 0.21/0.47    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d1_wellord2, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ B ) =>
% 0.21/0.47       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.47         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.47           ( ![C:$i,D:$i]:
% 0.21/0.47             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.47               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.47                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X11 : $i, X12 : $i]:
% 0.21/0.47         (((X12) != (k1_wellord2 @ X11))
% 0.21/0.47          | ((k3_relat_1 @ X12) = (X11))
% 0.21/0.47          | ~ (v1_relat_1 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X11 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k1_wellord2 @ X11))
% 0.21/0.47          | ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.47  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.47  thf('3', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('4', plain, (![X11 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(d6_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ( k3_relat_1 @ A ) =
% 0.21/0.47         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         (((k3_relat_1 @ X7)
% 0.21/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.47  thf(t7_xboole_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['5', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['4', '9'])).
% 0.21/0.47  thf('11', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, (![X11 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X11)) = (X11))),
% 0.21/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         (((k3_relat_1 @ X7)
% 0.21/0.47            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X2 : $i, X3 : $i]: (r1_tarski @ X2 @ (k2_xboole_0 @ X2 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.47  thf('18', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf(t11_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.47           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.21/0.47          | ~ (r1_tarski @ (k2_relat_1 @ X8) @ X10)
% 0.21/0.47          | (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.47          | (m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.21/0.47          | ~ (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, (![X15 : $i]: (v1_relat_1 @ (k1_wellord2 @ X15))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.21/0.47          | ~ (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.21/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.21/0.47          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '23'])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
