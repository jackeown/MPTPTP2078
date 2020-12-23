%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0RUrJgFgz

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  22 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   97 ( 113 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( ( k3_xboole_0 @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
        = ( k3_xboole_0 @ X19 @ ( k2_zfmisc_1 @ X20 @ ( k2_relat_1 @ X19 ) ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t98_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t98_relat_1])).

thf('4',plain,(
    ( k7_relat_1 @ sk_A @ ( k1_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    $false ),
    inference(simplify,[status(thm)],['7'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E0RUrJgFgz
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 12 iterations in 0.012s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.45  thf(t22_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( k3_xboole_0 @
% 0.22/0.45           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.45         ( A ) ) ))).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      (![X18 : $i]:
% 0.22/0.45         (((k3_xboole_0 @ X18 @ 
% 0.22/0.45            (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18))) = (
% 0.22/0.45            X18))
% 0.22/0.45          | ~ (v1_relat_1 @ X18))),
% 0.22/0.45      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.45  thf(t96_relat_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ B ) =>
% 0.22/0.45       ( ( k7_relat_1 @ B @ A ) =
% 0.22/0.45         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      (![X19 : $i, X20 : $i]:
% 0.22/0.45         (((k7_relat_1 @ X19 @ X20)
% 0.22/0.45            = (k3_xboole_0 @ X19 @ (k2_zfmisc_1 @ X20 @ (k2_relat_1 @ X19))))
% 0.22/0.45          | ~ (v1_relat_1 @ X19))),
% 0.22/0.45      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.22/0.45  thf('2', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 0.22/0.45          | ~ (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X0))),
% 0.22/0.45      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      (![X0 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.22/0.45      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.45  thf(t98_relat_1, conjecture,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i]:
% 0.22/0.45        ( ( v1_relat_1 @ A ) =>
% 0.22/0.45          ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t98_relat_1])).
% 0.22/0.45  thf('4', plain, (((k7_relat_1 @ sk_A @ (k1_relat_1 @ sk_A)) != (sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('5', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.45  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('7', plain, (((sk_A) != (sk_A))),
% 0.22/0.45      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain, ($false), inference('simplify', [status(thm)], ['7'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
