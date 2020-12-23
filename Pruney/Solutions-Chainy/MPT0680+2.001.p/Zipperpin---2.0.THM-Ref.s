%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.05TUHLVyES

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  47 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  244 ( 453 expanded)
%              Number of equality atoms :   17 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(t124_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i,C: $i] :
            ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) )
            = ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ! [B: $i,C: $i] :
              ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) )
              = ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
         => ( v2_funct_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_funct_1])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k6_subset_1 @ X5 @ X6 ) )
      = ( k6_subset_1 @ ( k9_relat_1 @ sk_A @ X5 ) @ ( k9_relat_1 @ sk_A @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k6_subset_1 @ X2 @ X3 )
      = ( k4_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ ( k9_relat_1 @ sk_A @ X5 ) @ ( k9_relat_1 @ sk_A @ X6 ) ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) @ ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) @ ( k9_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ ( k9_relat_1 @ sk_A @ X5 ) @ ( k9_relat_1 @ sk_A @ X6 ) ) ) ),
    inference(demod,[status(thm)],['1','2','3'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k9_relat_1 @ sk_A @ X1 ) @ ( k9_relat_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t122_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i,C: $i] :
            ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) )
            = ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k3_xboole_0 @ ( sk_B @ X4 ) @ ( sk_C @ X4 ) ) )
       != ( k3_xboole_0 @ ( k9_relat_1 @ X4 @ ( sk_B @ X4 ) ) @ ( k9_relat_1 @ X4 @ ( sk_C @ X4 ) ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t122_funct_1])).

thf('11',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) )
     != ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) )
     != ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    v2_funct_1 @ sk_A ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['0','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.05TUHLVyES
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 10 iterations in 0.010s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.43  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.43  thf(sk_C_type, type, sk_C: $i > $i).
% 0.19/0.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.43  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.19/0.43  thf(t124_funct_1, conjecture,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43       ( ( ![B:$i,C:$i]:
% 0.19/0.43           ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) =
% 0.19/0.43             ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) ) ) =>
% 0.19/0.43         ( v2_funct_1 @ A ) ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i]:
% 0.19/0.43        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43          ( ( ![B:$i,C:$i]:
% 0.19/0.43              ( ( k9_relat_1 @ A @ ( k6_subset_1 @ B @ C ) ) =
% 0.19/0.43                ( k6_subset_1 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) ) ) =>
% 0.19/0.43            ( v2_funct_1 @ A ) ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t124_funct_1])).
% 0.19/0.43  thf('0', plain, (~ (v2_funct_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      (![X5 : $i, X6 : $i]:
% 0.19/0.43         ((k9_relat_1 @ sk_A @ (k6_subset_1 @ X5 @ X6))
% 0.19/0.43           = (k6_subset_1 @ (k9_relat_1 @ sk_A @ X5) @ (k9_relat_1 @ sk_A @ X6)))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(redefinition_k6_subset_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.19/0.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.43  thf('3', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i]: ((k6_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))),
% 0.19/0.43      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      (![X5 : $i, X6 : $i]:
% 0.19/0.43         ((k9_relat_1 @ sk_A @ (k4_xboole_0 @ X5 @ X6))
% 0.19/0.43           = (k4_xboole_0 @ (k9_relat_1 @ sk_A @ X5) @ (k9_relat_1 @ sk_A @ X6)))),
% 0.19/0.43      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.19/0.43  thf(t48_xboole_1, axiom,
% 0.19/0.43    (![A:$i,B:$i]:
% 0.19/0.43     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.43  thf('5', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.43           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         ((k4_xboole_0 @ (k9_relat_1 @ sk_A @ X1) @ 
% 0.19/0.43           (k9_relat_1 @ sk_A @ (k4_xboole_0 @ X1 @ X0)))
% 0.19/0.43           = (k3_xboole_0 @ (k9_relat_1 @ sk_A @ X1) @ (k9_relat_1 @ sk_A @ X0)))),
% 0.19/0.43      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      (![X5 : $i, X6 : $i]:
% 0.19/0.43         ((k9_relat_1 @ sk_A @ (k4_xboole_0 @ X5 @ X6))
% 0.19/0.43           = (k4_xboole_0 @ (k9_relat_1 @ sk_A @ X5) @ (k9_relat_1 @ sk_A @ X6)))),
% 0.19/0.43      inference('demod', [status(thm)], ['1', '2', '3'])).
% 0.19/0.43  thf('8', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.43           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.43  thf('9', plain,
% 0.19/0.43      (![X0 : $i, X1 : $i]:
% 0.19/0.43         ((k9_relat_1 @ sk_A @ (k3_xboole_0 @ X1 @ X0))
% 0.19/0.43           = (k3_xboole_0 @ (k9_relat_1 @ sk_A @ X1) @ (k9_relat_1 @ sk_A @ X0)))),
% 0.19/0.43      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.19/0.43  thf(t122_funct_1, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.43       ( ( ![B:$i,C:$i]:
% 0.19/0.43           ( ( k9_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.19/0.43             ( k3_xboole_0 @ ( k9_relat_1 @ A @ B ) @ ( k9_relat_1 @ A @ C ) ) ) ) =>
% 0.19/0.43         ( v2_funct_1 @ A ) ) ))).
% 0.19/0.43  thf('10', plain,
% 0.19/0.43      (![X4 : $i]:
% 0.19/0.43         (((k9_relat_1 @ X4 @ (k3_xboole_0 @ (sk_B @ X4) @ (sk_C @ X4)))
% 0.19/0.43            != (k3_xboole_0 @ (k9_relat_1 @ X4 @ (sk_B @ X4)) @ 
% 0.19/0.43                (k9_relat_1 @ X4 @ (sk_C @ X4))))
% 0.19/0.43          | (v2_funct_1 @ X4)
% 0.19/0.43          | ~ (v1_funct_1 @ X4)
% 0.19/0.43          | ~ (v1_relat_1 @ X4))),
% 0.19/0.43      inference('cnf', [status(esa)], [t122_funct_1])).
% 0.19/0.43  thf('11', plain,
% 0.19/0.43      ((((k9_relat_1 @ sk_A @ (k3_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)))
% 0.19/0.43          != (k9_relat_1 @ sk_A @ (k3_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A))))
% 0.19/0.43        | ~ (v1_relat_1 @ sk_A)
% 0.19/0.43        | ~ (v1_funct_1 @ sk_A)
% 0.19/0.43        | (v2_funct_1 @ sk_A))),
% 0.19/0.43      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.43  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('14', plain,
% 0.19/0.43      ((((k9_relat_1 @ sk_A @ (k3_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)))
% 0.19/0.43          != (k9_relat_1 @ sk_A @ (k3_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A))))
% 0.19/0.43        | (v2_funct_1 @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.43  thf('15', plain, ((v2_funct_1 @ sk_A)),
% 0.19/0.43      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.43  thf('16', plain, ($false), inference('demod', [status(thm)], ['0', '15'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
