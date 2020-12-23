%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AcmQfRXvnB

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  249 ( 501 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X8 @ ( k10_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k2_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ X11 @ ( k10_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k9_relat_1 @ X7 @ X5 ) @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
    = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AcmQfRXvnB
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 38 iterations in 0.045s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.50  thf(t158_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.50           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.50         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.50              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.50            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.21/0.50  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t145_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((r1_tarski @ (k9_relat_1 @ X8 @ (k10_relat_1 @ X8 @ X9)) @ X9)
% 0.21/0.50          | ~ (v1_funct_1 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t145_funct_1])).
% 0.21/0.50  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t147_funct_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.50         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X10 @ (k2_relat_1 @ X11))
% 0.21/0.50          | ((k9_relat_1 @ X11 @ (k10_relat_1 @ X11 @ X10)) = (X10))
% 0.21/0.50          | ~ (v1_funct_1 @ X11)
% 0.21/0.50          | ~ (v1_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.50        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t156_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.50         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X7)
% 0.21/0.50          | (r1_tarski @ (k9_relat_1 @ X7 @ X5) @ (k9_relat_1 @ X7 @ X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.50           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.50      inference('sup+', [status(thm)], ['7', '10'])).
% 0.21/0.50  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((k2_xboole_0 @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.21/0.50         = (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf(t11_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) @ X0)
% 0.21/0.50          | (r1_tarski @ sk_A @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.50        | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '17'])).
% 0.21/0.50  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.50  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
