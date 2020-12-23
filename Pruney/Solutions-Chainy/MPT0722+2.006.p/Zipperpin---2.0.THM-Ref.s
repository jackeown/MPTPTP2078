%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xFkxIepofL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  43 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :  163 ( 415 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t177_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v2_funct_1 @ A )
              & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
           => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
              = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t177_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k1_relat_1 @ X3 ) )
      | ~ ( v2_funct_1 @ X3 )
      | ( ( k10_relat_1 @ X3 @ ( k9_relat_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('8',plain,(
    ( k9_relat_1 @ ( k2_funct_1 @ sk_A ) @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ( k10_relat_1 @ sk_A @ ( k9_relat_1 @ sk_A @ sk_B ) )
 != sk_B ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['6','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xFkxIepofL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:59:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 7 iterations in 0.008s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.46  thf(t177_funct_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.19/0.46           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.19/0.46             ( B ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.19/0.46              ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.19/0.46                ( B ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t177_funct_1])).
% 0.19/0.46  thf('0', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t164_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.19/0.46         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r1_tarski @ X2 @ (k1_relat_1 @ X3))
% 0.19/0.46          | ~ (v2_funct_1 @ X3)
% 0.19/0.46          | ((k10_relat_1 @ X3 @ (k9_relat_1 @ X3 @ X2)) = (X2))
% 0.19/0.46          | ~ (v1_funct_1 @ X3)
% 0.19/0.46          | ~ (v1_relat_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_A)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_A)
% 0.19/0.46        | ((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) = (sk_B))
% 0.19/0.46        | ~ (v2_funct_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((v2_funct_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5'])).
% 0.19/0.46  thf(t155_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.46       ( ( v2_funct_1 @ B ) =>
% 0.19/0.46         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v2_funct_1 @ X0)
% 0.19/0.46          | ((k10_relat_1 @ X0 @ X1) = (k9_relat_1 @ (k2_funct_1 @ X0) @ X1))
% 0.19/0.46          | ~ (v1_funct_1 @ X0)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (((k9_relat_1 @ (k2_funct_1 @ sk_A) @ (k9_relat_1 @ sk_A @ sk_B))
% 0.19/0.46         != (sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) != (sk_B))
% 0.19/0.46        | ~ (v1_relat_1 @ sk_A)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_A)
% 0.19/0.46        | ~ (v2_funct_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain, ((v2_funct_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (((k10_relat_1 @ sk_A @ (k9_relat_1 @ sk_A @ sk_B)) != (sk_B))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.19/0.46  thf('14', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['6', '13'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
