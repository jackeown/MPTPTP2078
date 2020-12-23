%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O618uoHEjv

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  363 ( 603 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ C @ A )
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X24 @ X23 ) @ X25 )
        = ( k1_funct_1 @ X23 @ ( k1_funct_1 @ X24 @ X25 ) ) )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
       != ( k6_relat_1 @ X26 ) )
      | ( ( k1_funct_1 @ X27 @ X28 )
        = X28 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('16',plain,(
    ! [X26: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X26 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X26 ) )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X26 ) @ X28 )
        = X28 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('18',plain,(
    ! [X22: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X26: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X26 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X26 ) @ X28 )
        = X28 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_A )
     != ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_A )
 != ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O618uoHEjv
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:03:36 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 117 iterations in 0.075s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t38_funct_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.49         ( ( k1_funct_1 @ C @ A ) =
% 0.19/0.49           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.49            ( ( k1_funct_1 @ C @ A ) =
% 0.19/0.49              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(commutativity_k3_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_2)))),
% 0.19/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.49  thf(t17_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.19/0.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.49  thf(d3_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X2 @ X3)
% 0.19/0.49          | (r2_hidden @ X2 @ X4)
% 0.19/0.49          | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.49  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.49  thf(t71_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.49  thf('7', plain, (![X19 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 0.19/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.49  thf(t23_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.49           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.49             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.19/0.49               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X23)
% 0.19/0.49          | ~ (v1_funct_1 @ X23)
% 0.19/0.49          | ((k1_funct_1 @ (k5_relat_1 @ X24 @ X23) @ X25)
% 0.19/0.49              = (k1_funct_1 @ X23 @ (k1_funct_1 @ X24 @ X25)))
% 0.19/0.49          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.19/0.49          | ~ (v1_funct_1 @ X24)
% 0.19/0.49          | ~ (v1_relat_1 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.19/0.49              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.19/0.49          | ~ (v1_funct_1 @ X2)
% 0.19/0.49          | ~ (v1_relat_1 @ X2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf(fc3_funct_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.49  thf('10', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('11', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.19/0.49              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.19/0.49          | ~ (v1_funct_1 @ X2)
% 0.19/0.49          | ~ (v1_relat_1 @ X2))),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_funct_1 @ X0)
% 0.19/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.19/0.49              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '12'])).
% 0.19/0.49  thf('14', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.49  thf(t34_funct_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.49       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.19/0.49         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.49         (((X27) != (k6_relat_1 @ X26))
% 0.19/0.49          | ((k1_funct_1 @ X27 @ X28) = (X28))
% 0.19/0.49          | ~ (r2_hidden @ X28 @ X26)
% 0.19/0.49          | ~ (v1_funct_1 @ X27)
% 0.19/0.49          | ~ (v1_relat_1 @ X27))),
% 0.19/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X26 : $i, X28 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ (k6_relat_1 @ X26))
% 0.19/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X26))
% 0.19/0.49          | ~ (r2_hidden @ X28 @ X26)
% 0.19/0.49          | ((k1_funct_1 @ (k6_relat_1 @ X26) @ X28) = (X28)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.49  thf('17', plain, (![X21 : $i]: (v1_relat_1 @ (k6_relat_1 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('18', plain, (![X22 : $i]: (v1_funct_1 @ (k6_relat_1 @ X22))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X26 : $i, X28 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X28 @ X26)
% 0.19/0.49          | ((k1_funct_1 @ (k6_relat_1 @ X26) @ X28) = (X28)))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.19/0.49  thf('20', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_funct_1 @ X0)
% 0.19/0.49          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.19/0.49              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((k1_funct_1 @ sk_C_2 @ sk_A)
% 0.19/0.49         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C_2) @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.19/0.49        | ~ (v1_funct_1 @ sk_C_2)
% 0.19/0.49        | ~ (v1_relat_1 @ sk_C_2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf('24', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('25', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.49  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
