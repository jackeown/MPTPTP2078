%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wSopWz0Lz6

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 (  45 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  229 ( 415 expanded)
%              Number of equality atoms :   16 (  27 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t168_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t168_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ( ( k9_relat_1 @ X4 @ ( k2_tarski @ X3 @ X5 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X4 @ X3 ) @ ( k1_funct_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) )
        = ( k9_relat_1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,(
    ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wSopWz0Lz6
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 8 iterations in 0.009s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(t168_funct_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48         ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.22/0.48           ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i]:
% 0.22/0.48        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.48          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48            ( ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) =
% 0.22/0.48              ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t168_funct_1])).
% 0.22/0.48  thf('0', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t118_funct_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.48       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.48           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.22/0.48         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.22/0.48           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.22/0.48          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.22/0.48          | ((k9_relat_1 @ X4 @ (k2_tarski @ X3 @ X5))
% 0.22/0.48              = (k2_tarski @ (k1_funct_1 @ X4 @ X3) @ (k1_funct_1 @ X4 @ X5)))
% 0.22/0.48          | ~ (v1_funct_1 @ X4)
% 0.22/0.48          | ~ (v1_relat_1 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ sk_B)
% 0.22/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.22/0.48              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.48                 (k1_funct_1 @ sk_B @ X0)))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.22/0.48            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.22/0.48               (k1_funct_1 @ sk_B @ X0)))
% 0.22/0.48          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.22/0.48         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '6'])).
% 0.22/0.48  thf(t69_enumset1, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.48  thf('8', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf('9', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.48         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.48  thf(t148_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i]:
% 0.22/0.48         (((k2_relat_1 @ (k7_relat_1 @ X1 @ X2)) = (k9_relat_1 @ X1 @ X2))
% 0.22/0.48          | ~ (v1_relat_1 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.22/0.48         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.48          != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.22/0.48         != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['10', '15'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
