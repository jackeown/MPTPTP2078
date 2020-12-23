%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMrWJ5y1q2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   12 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  137 ( 163 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ X3 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( r1_tarski @ ( k9_relat_1 @ X5 @ X6 ) @ ( k9_relat_1 @ X4 @ X6 ) )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X0 @ X2 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(t120_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_funct_1])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    $false ),
    inference(demod,[status(thm)],['7','8'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JMrWJ5y1q2
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:51:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 6 iterations in 0.009s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(t117_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i]:
% 0.21/0.46         ((r1_tarski @ (k8_relat_1 @ X2 @ X3) @ X3) | ~ (v1_relat_1 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.21/0.46  thf(t157_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ![C:$i]:
% 0.21/0.46         ( ( v1_relat_1 @ C ) =>
% 0.21/0.46           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.46             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X4)
% 0.21/0.46          | (r1_tarski @ (k9_relat_1 @ X5 @ X6) @ (k9_relat_1 @ X4 @ X6))
% 0.21/0.46          | ~ (r1_tarski @ X5 @ X4)
% 0.21/0.46          | ~ (v1_relat_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t157_relat_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.46          | (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2) @ 
% 0.21/0.46             (k9_relat_1 @ X0 @ X2))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2) @ 
% 0.21/0.46           (k9_relat_1 @ X0 @ X2))
% 0.21/0.46          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.46  thf(dt_k8_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         ((v1_relat_1 @ (k8_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (v1_relat_1 @ X0)
% 0.21/0.46          | (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ X1 @ X0) @ X2) @ 
% 0.21/0.46             (k9_relat_1 @ X0 @ X2)))),
% 0.21/0.46      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf(t120_funct_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46       ( r1_tarski @
% 0.21/0.46         ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ ( k9_relat_1 @ C @ B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46          ( r1_tarski @
% 0.21/0.46            ( k9_relat_1 @ ( k8_relat_1 @ A @ C ) @ B ) @ 
% 0.21/0.46            ( k9_relat_1 @ C @ B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t120_funct_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (~ (r1_tarski @ (k9_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_B) @ 
% 0.21/0.46          (k9_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('7', plain, (~ (v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, ($false), inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
