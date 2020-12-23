%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4n8tFpfz82

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 ( 365 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t163_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t163_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('5',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X7 @ X8 ) @ ( k10_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r1_tarski @ X10 @ ( k10_relat_1 @ X11 @ ( k9_relat_1 @ X11 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ X0 @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4n8tFpfz82
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 42 iterations in 0.023s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.43  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.43  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.43  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.43  thf(t163_funct_1, conjecture,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.43       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.43           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.43         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.43        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.43          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.43              ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.20/0.43            ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t163_funct_1])).
% 0.20/0.43  thf('0', plain, (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('1', plain, ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t12_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i]:
% 0.20/0.43         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.20/0.43      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (((k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (((k2_xboole_0 @ sk_B @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_B))),
% 0.20/0.43      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.43  thf(t175_relat_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ C ) =>
% 0.20/0.43       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.43         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.43         (((k10_relat_1 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.20/0.43            = (k2_xboole_0 @ (k10_relat_1 @ X7 @ X8) @ (k10_relat_1 @ X7 @ X9)))
% 0.20/0.43          | ~ (v1_relat_1 @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.20/0.43  thf('7', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(t146_funct_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ B ) =>
% 0.20/0.43       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.43         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X10 : $i, X11 : $i]:
% 0.20/0.43         (~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.43          | (r1_tarski @ X10 @ (k10_relat_1 @ X11 @ (k9_relat_1 @ X11 @ X10)))
% 0.20/0.43          | ~ (v1_relat_1 @ X11))),
% 0.20/0.43      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.43  thf('9', plain,
% 0.20/0.43      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.43        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.43      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.43  thf(t10_xboole_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.20/0.43  thf('12', plain,
% 0.20/0.43      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.43         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.20/0.43  thf('13', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (r1_tarski @ sk_A @ 
% 0.20/0.43          (k2_xboole_0 @ X0 @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.43      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.43  thf('14', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_A @ 
% 0.20/0.43           (k10_relat_1 @ sk_C @ 
% 0.20/0.43            (k2_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A))))
% 0.20/0.43          | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.43      inference('sup+', [status(thm)], ['6', '13'])).
% 0.20/0.43  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('16', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (r1_tarski @ sk_A @ 
% 0.20/0.43          (k10_relat_1 @ sk_C @ (k2_xboole_0 @ X0 @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.43      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.43  thf('17', plain, ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.20/0.43      inference('sup+', [status(thm)], ['5', '16'])).
% 0.20/0.43  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
