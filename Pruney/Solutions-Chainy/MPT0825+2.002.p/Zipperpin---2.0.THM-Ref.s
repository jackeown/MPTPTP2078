%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UZW7QBCYKf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   80 (  90 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t28_relset_1,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k6_relat_1 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    $false ),
    inference(demod,[status(thm)],['0','6'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UZW7QBCYKf
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.44  % Solved by: fo/fo7.sh
% 0.22/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.44  % done 5 iterations in 0.009s
% 0.22/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.44  % SZS output start Refutation
% 0.22/0.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.44  thf(t28_relset_1, conjecture,
% 0.22/0.44    (![A:$i]: ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.22/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.44    (~( ![A:$i]: ( r1_tarski @ ( k6_relat_1 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.22/0.44    inference('cnf.neg', [status(esa)], [t28_relset_1])).
% 0.22/0.44  thf('0', plain,
% 0.22/0.44      (~ (r1_tarski @ (k6_relat_1 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.22/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.44  thf(t71_relat_1, axiom,
% 0.22/0.44    (![A:$i]:
% 0.22/0.44     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.44       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.44  thf('1', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.22/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.44  thf(t21_relat_1, axiom,
% 0.22/0.44    (![A:$i]:
% 0.22/0.44     ( ( v1_relat_1 @ A ) =>
% 0.22/0.44       ( r1_tarski @
% 0.22/0.44         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.44  thf('2', plain,
% 0.22/0.44      (![X1 : $i]:
% 0.22/0.44         ((r1_tarski @ X1 @ 
% 0.22/0.44           (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1)))
% 0.22/0.44          | ~ (v1_relat_1 @ X1))),
% 0.22/0.44      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.44  thf('3', plain,
% 0.22/0.44      (![X0 : $i]:
% 0.22/0.44         ((r1_tarski @ (k6_relat_1 @ X0) @ 
% 0.22/0.44           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.22/0.44          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.22/0.44      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.44  thf('4', plain, (![X3 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.22/0.44      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.44  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.44  thf('5', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.22/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.44  thf('6', plain,
% 0.22/0.44      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.22/0.44      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.44  thf('7', plain, ($false), inference('demod', [status(thm)], ['0', '6'])).
% 0.22/0.44  
% 0.22/0.44  % SZS output end Refutation
% 0.22/0.44  
% 0.22/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
