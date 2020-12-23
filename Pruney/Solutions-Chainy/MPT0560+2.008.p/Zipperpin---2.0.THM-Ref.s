%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noeIlseimX

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:39 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   15 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  229 ( 295 expanded)
%              Number of equality atoms :   20 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X8 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k9_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t162_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ B @ C )
           => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
              = ( k9_relat_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_relat_1])).

thf('8',plain,(
    ( k9_relat_1 @ ( k7_relat_1 @ sk_A @ sk_C ) @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k9_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) )
     != ( k9_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ( k9_relat_1 @ sk_A @ sk_B )
 != ( k9_relat_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['9','14','15'])).

thf('17',plain,(
    $false ),
    inference(simplify,[status(thm)],['16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.noeIlseimX
% 0.16/0.37  % Computer   : n012.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 09:19:22 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.51  % Solved by: fo/fo7.sh
% 0.24/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.51  % done 32 iterations in 0.035s
% 0.24/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.51  % SZS output start Refutation
% 0.24/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.24/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.51  thf(t148_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ B ) =>
% 0.24/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.24/0.51  thf('0', plain,
% 0.24/0.51      (![X9 : $i, X10 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.24/0.51          | ~ (v1_relat_1 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.24/0.51  thf(t100_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i,C:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ C ) =>
% 0.24/0.51       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.24/0.51         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.24/0.51  thf('1', plain,
% 0.24/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.24/0.51         (((k7_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X8)
% 0.24/0.51            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ X7 @ X8)))
% 0.24/0.51          | ~ (v1_relat_1 @ X6))),
% 0.24/0.51      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.24/0.51  thf('2', plain,
% 0.24/0.51      (![X9 : $i, X10 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.24/0.51          | ~ (v1_relat_1 @ X9))),
% 0.24/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.24/0.51  thf('3', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.51            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X2)
% 0.24/0.51          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.24/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.51  thf(dt_k7_relat_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.24/0.51  thf('4', plain,
% 0.24/0.51      (![X4 : $i, X5 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X4) | (v1_relat_1 @ (k7_relat_1 @ X4 @ X5)))),
% 0.24/0.51      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.24/0.51  thf('5', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X2)
% 0.24/0.51          | ((k2_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.51              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.24/0.51      inference('clc', [status(thm)], ['3', '4'])).
% 0.24/0.51  thf('6', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.51            = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.24/0.51          | ~ (v1_relat_1 @ X2)
% 0.24/0.51          | ~ (v1_relat_1 @ X2))),
% 0.24/0.51      inference('sup+', [status(thm)], ['0', '5'])).
% 0.24/0.51  thf('7', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.51         (~ (v1_relat_1 @ X2)
% 0.24/0.51          | ((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.51              = (k9_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)))),
% 0.24/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.24/0.51  thf(t162_relat_1, conjecture,
% 0.24/0.51    (![A:$i]:
% 0.24/0.51     ( ( v1_relat_1 @ A ) =>
% 0.24/0.51       ( ![B:$i,C:$i]:
% 0.24/0.51         ( ( r1_tarski @ B @ C ) =>
% 0.24/0.51           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.24/0.51             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.24/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.51    (~( ![A:$i]:
% 0.24/0.51        ( ( v1_relat_1 @ A ) =>
% 0.24/0.51          ( ![B:$i,C:$i]:
% 0.24/0.51            ( ( r1_tarski @ B @ C ) =>
% 0.24/0.51              ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.24/0.51                ( k9_relat_1 @ A @ B ) ) ) ) ) )),
% 0.24/0.51    inference('cnf.neg', [status(esa)], [t162_relat_1])).
% 0.24/0.51  thf('8', plain,
% 0.24/0.51      (((k9_relat_1 @ (k7_relat_1 @ sk_A @ sk_C) @ sk_B)
% 0.24/0.51         != (k9_relat_1 @ sk_A @ sk_B))),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('9', plain,
% 0.24/0.51      ((((k9_relat_1 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B))
% 0.24/0.51          != (k9_relat_1 @ sk_A @ sk_B))
% 0.24/0.51        | ~ (v1_relat_1 @ sk_A))),
% 0.24/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.51  thf('10', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf(t28_xboole_1, axiom,
% 0.24/0.51    (![A:$i,B:$i]:
% 0.24/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.51  thf('11', plain,
% 0.24/0.51      (![X2 : $i, X3 : $i]:
% 0.24/0.51         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.24/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.51  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.24/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.24/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.24/0.51  thf('13', plain,
% 0.24/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.24/0.51  thf('14', plain, (((k3_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.24/0.51  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.51  thf('16', plain,
% 0.24/0.51      (((k9_relat_1 @ sk_A @ sk_B) != (k9_relat_1 @ sk_A @ sk_B))),
% 0.24/0.51      inference('demod', [status(thm)], ['9', '14', '15'])).
% 0.24/0.51  thf('17', plain, ($false), inference('simplify', [status(thm)], ['16'])).
% 0.24/0.51  
% 0.24/0.51  % SZS output end Refutation
% 0.24/0.51  
% 0.24/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
