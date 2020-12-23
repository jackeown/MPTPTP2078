%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xZz5PnRaOi

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  40 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  252 ( 352 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t141_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_xboole_0 @ B @ C )
         => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_xboole_0 @ B @ C )
           => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t141_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k10_relat_1 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X8 @ X9 ) @ ( k10_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( sk_C @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xZz5PnRaOi
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 19 iterations in 0.026s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.47  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(t141_funct_1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ![B:$i,C:$i]:
% 0.21/0.47         ( ( r1_xboole_0 @ B @ C ) =>
% 0.21/0.47           ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47          ( ![B:$i,C:$i]:
% 0.21/0.47            ( ( r1_xboole_0 @ B @ C ) =>
% 0.21/0.47              ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t141_funct_1])).
% 0.21/0.47  thf('0', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t137_funct_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.21/0.47         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (((k10_relat_1 @ X8 @ (k3_xboole_0 @ X9 @ X10))
% 0.21/0.47            = (k3_xboole_0 @ (k10_relat_1 @ X8 @ X9) @ (k10_relat_1 @ X8 @ X10)))
% 0.21/0.47          | ~ (v1_funct_1 @ X8)
% 0.21/0.47          | ~ (v1_relat_1 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.21/0.47  thf(t4_xboole_0, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.47          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ 
% 0.21/0.47           (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1)) @ 
% 0.21/0.47           (k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf(t166_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ C ) =>
% 0.21/0.47       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.21/0.47         ( ?[D:$i]:
% 0.21/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.47             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.21/0.47             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.21/0.47          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | (r2_hidden @ 
% 0.21/0.47             (sk_D @ X2 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.21/0.47              (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1))) @ 
% 0.21/0.47             (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ 
% 0.21/0.47           (sk_D @ X2 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.21/0.47            (sk_C @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1))) @ 
% 0.21/0.47           (k3_xboole_0 @ X1 @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.21/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         ((r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0))
% 0.21/0.47          | ~ (v1_funct_1 @ X2)
% 0.21/0.47          | ~ (v1_relat_1 @ X2)
% 0.21/0.47          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.21/0.47             (k10_relat_1 @ X0 @ sk_C_1)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (~ (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_B) @ 
% 0.21/0.47          (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ((~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, ((v1_funct_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ($false),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
