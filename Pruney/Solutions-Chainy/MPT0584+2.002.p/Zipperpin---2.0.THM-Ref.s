%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sxrkywODM

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  48 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  225 ( 474 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t188_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r1_tarski @ C @ D )
                & ( ( k7_relat_1 @ A @ D )
                  = ( k7_relat_1 @ B @ D ) ) )
             => ( ( k7_relat_1 @ A @ C )
                = ( k7_relat_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( r1_tarski @ C @ D )
                  & ( ( k7_relat_1 @ A @ D )
                    = ( k7_relat_1 @ B @ D ) ) )
               => ( ( k7_relat_1 @ A @ C )
                  = ( k7_relat_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t188_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X8 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('5',plain,
    ( ( k7_relat_1 @ sk_A @ sk_D )
    = ( k7_relat_1 @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) @ X8 )
        = ( k7_relat_1 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_D ) @ X0 )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_D ) @ X0 )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
        = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ X0 ) )
      = ( k7_relat_1 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['3','12'])).

thf('14',plain,
    ( ( k7_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_D @ sk_C ) )
    = ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = sk_C ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,
    ( ( k7_relat_1 @ sk_A @ sk_C )
    = ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ( k7_relat_1 @ sk_A @ sk_C )
 != ( k7_relat_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8sxrkywODM
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:58:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 21 iterations in 0.025s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.52  thf(t188_relat_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( v1_relat_1 @ B ) =>
% 0.22/0.52           ( ![C:$i,D:$i]:
% 0.22/0.52             ( ( ( r1_tarski @ C @ D ) & 
% 0.22/0.52                 ( ( k7_relat_1 @ A @ D ) = ( k7_relat_1 @ B @ D ) ) ) =>
% 0.22/0.52               ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( v1_relat_1 @ A ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( v1_relat_1 @ B ) =>
% 0.22/0.52              ( ![C:$i,D:$i]:
% 0.22/0.52                ( ( ( r1_tarski @ C @ D ) & 
% 0.22/0.52                    ( ( k7_relat_1 @ A @ D ) = ( k7_relat_1 @ B @ D ) ) ) =>
% 0.22/0.52                  ( ( k7_relat_1 @ A @ C ) = ( k7_relat_1 @ B @ C ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t188_relat_1])).
% 0.22/0.52  thf('0', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t28_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.52  thf('2', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf(t100_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.52         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         (((k7_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X8)
% 0.22/0.52            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ X7 @ X8)))
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.52  thf('5', plain, (((k7_relat_1 @ sk_A @ sk_D) = (k7_relat_1 @ sk_B @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.52         (((k7_relat_1 @ (k7_relat_1 @ X6 @ X7) @ X8)
% 0.22/0.52            = (k7_relat_1 @ X6 @ (k3_xboole_0 @ X7 @ X8)))
% 0.22/0.52          | ~ (v1_relat_1 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_D) @ X0)
% 0.22/0.52            = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_D) @ X0)
% 0.22/0.52           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_D @ X0))
% 0.22/0.52            = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))
% 0.22/0.52          | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.52      inference('sup+', [status(thm)], ['4', '9'])).
% 0.22/0.52  thf('11', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_D @ X0))
% 0.22/0.52           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ sk_D @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_D @ X0))
% 0.22/0.52           = (k7_relat_1 @ sk_B @ (k3_xboole_0 @ X0 @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((k7_relat_1 @ sk_A @ (k3_xboole_0 @ sk_D @ sk_C))
% 0.22/0.52         = (k7_relat_1 @ sk_B @ sk_C))),
% 0.22/0.52      inference('sup+', [status(thm)], ['2', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.52  thf('16', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (sk_C))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('17', plain, (((k7_relat_1 @ sk_A @ sk_C) = (k7_relat_1 @ sk_B @ sk_C))),
% 0.22/0.52      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((k7_relat_1 @ sk_A @ sk_C) != (k7_relat_1 @ sk_B @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
