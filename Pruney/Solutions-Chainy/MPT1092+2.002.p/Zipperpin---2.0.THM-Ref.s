%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SASpePhV1R

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  28 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  101 ( 161 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t26_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
         => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_finset_1])).

thf('0',plain,(
    ~ ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t17_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_finset_1 @ A )
       => ( v1_finset_1 @ ( k9_relat_1 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_finset_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t17_finset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_finset_1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_finset_1 @ ( k2_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SASpePhV1R
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 7 iterations in 0.005s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(t26_finset_1, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.46         ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.46          ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.46            ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t26_finset_1])).
% 0.21/0.46  thf('0', plain, (~ (v1_finset_1 @ (k2_relat_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((v1_finset_1 @ (k1_relat_1 @ sk_A))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t146_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.46  thf(t17_finset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.46       ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k9_relat_1 @ B @ A ) ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_finset_1 @ X1)
% 0.21/0.46          | ~ (v1_relat_1 @ X2)
% 0.21/0.46          | ~ (v1_funct_1 @ X2)
% 0.21/0.46          | (v1_finset_1 @ (k9_relat_1 @ X2 @ X1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t17_finset_1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v1_finset_1 @ (k2_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_finset_1 @ (k1_relat_1 @ X0)))),
% 0.21/0.46      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (v1_finset_1 @ (k1_relat_1 @ X0))
% 0.21/0.46          | ~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | (v1_finset_1 @ (k2_relat_1 @ X0)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((v1_finset_1 @ (k2_relat_1 @ sk_A))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '5'])).
% 0.21/0.46  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, ((v1_finset_1 @ (k2_relat_1 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.21/0.46  thf('10', plain, ($false), inference('demod', [status(thm)], ['0', '9'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
