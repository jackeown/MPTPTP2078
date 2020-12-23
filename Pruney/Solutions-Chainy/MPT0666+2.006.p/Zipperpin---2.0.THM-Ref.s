%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fDMzQBlo1O

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  298 ( 634 expanded)
%              Number of equality atoms :   29 (  57 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t82_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = ( k7_relat_1 @ C @ A ) )
          & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r1_tarski @ A @ B )
         => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
              = ( k7_relat_1 @ C @ A ) )
            & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
              = ( k7_relat_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_funct_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X7 @ X6 ) @ X5 )
        = ( k7_relat_1 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X3 ) @ X4 )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('6',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('7',plain,
    ( ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
       != ( k7_relat_1 @ sk_C @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
   <= ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,
    ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B )
     != ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['4','15'])).

thf('17',plain,
    ( ( ( k7_relat_1 @ sk_C @ sk_A )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fDMzQBlo1O
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 20 iterations in 0.020s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(t82_funct_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46         ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.46             ( k7_relat_1 @ C @ A ) ) & 
% 0.21/0.46           ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.21/0.46             ( k7_relat_1 @ C @ A ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46            ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.46                ( k7_relat_1 @ C @ A ) ) & 
% 0.21/0.46              ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.21/0.46                ( k7_relat_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t82_funct_1])).
% 0.21/0.46  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t103_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X5 @ X6)
% 0.21/0.46          | ~ (v1_relat_1 @ X7)
% 0.21/0.46          | ((k7_relat_1 @ (k7_relat_1 @ X7 @ X6) @ X5)
% 0.21/0.46              = (k7_relat_1 @ X7 @ X5)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.46            = (k7_relat_1 @ X0 @ sk_A))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46          != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.46        | ((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46            != (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf(t100_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.46         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.46         (((k7_relat_1 @ (k7_relat_1 @ X2 @ X3) @ X4)
% 0.21/0.46            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X3 @ X4)))
% 0.21/0.46          | ~ (v1_relat_1 @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46          != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.46           != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.46         | ~ (v1_relat_1 @ sk_C)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t28_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.46  thf('10', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A)))
% 0.21/0.46         <= (~
% 0.21/0.46             (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46                = (k7_relat_1 @ sk_C @ sk_A))))),
% 0.21/0.46      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      ((((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (~
% 0.21/0.46       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46          = (k7_relat_1 @ sk_C @ sk_A))) | 
% 0.21/0.46       ~
% 0.21/0.46       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B)
% 0.21/0.46          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.46      inference('split', [status(esa)], ['3'])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (~
% 0.21/0.46       (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46          = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.21/0.46      inference('sat_resolution*', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.21/0.46         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.46      inference('simpl_trail', [status(thm)], ['4', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      ((((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '16'])).
% 0.21/0.46  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.46  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
