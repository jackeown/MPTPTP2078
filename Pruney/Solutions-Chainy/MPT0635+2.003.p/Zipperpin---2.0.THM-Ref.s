%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TYdqViVHja

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:51 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  354 ( 637 expanded)
%              Number of equality atoms :   24 (  41 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
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

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X17 @ X16 ) @ X18 )
        = ( k1_funct_1 @ X16 @ ( k1_funct_1 @ X17 @ X18 ) ) )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('15',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t35_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A )
        = A ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( k6_relat_1 @ X20 ) @ X19 )
        = X19 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_1])).

thf('20',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_A )
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TYdqViVHja
% 0.16/0.38  % Computer   : n015.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 14:05:08 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.25/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.54  % Solved by: fo/fo7.sh
% 0.25/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.54  % done 95 iterations in 0.050s
% 0.25/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.54  % SZS output start Refutation
% 0.25/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.25/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.25/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.25/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.25/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.25/0.54  thf(t38_funct_1, conjecture,
% 0.25/0.54    (![A:$i,B:$i,C:$i]:
% 0.25/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.54       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.25/0.54         ( ( k1_funct_1 @ C @ A ) =
% 0.25/0.54           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.25/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.54        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.54          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.25/0.54            ( ( k1_funct_1 @ C @ A ) =
% 0.25/0.54              ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )),
% 0.25/0.54    inference('cnf.neg', [status(esa)], [t38_funct_1])).
% 0.25/0.54  thf('0', plain,
% 0.25/0.54      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf(commutativity_k2_tarski, axiom,
% 0.25/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.25/0.54  thf('1', plain,
% 0.25/0.54      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.25/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.25/0.54  thf(t12_setfam_1, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.25/0.54  thf('2', plain,
% 0.25/0.54      (![X10 : $i, X11 : $i]:
% 0.25/0.54         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.25/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.25/0.54  thf('3', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i]:
% 0.25/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.54      inference('sup+', [status(thm)], ['1', '2'])).
% 0.25/0.54  thf('4', plain,
% 0.25/0.54      (![X10 : $i, X11 : $i]:
% 0.25/0.54         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.25/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.25/0.54  thf('5', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.25/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.25/0.54  thf('6', plain,
% 0.25/0.54      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 0.25/0.54      inference('demod', [status(thm)], ['0', '5'])).
% 0.25/0.54  thf(t17_xboole_1, axiom,
% 0.25/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.25/0.54  thf('7', plain,
% 0.25/0.54      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.25/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.25/0.54  thf(d3_tarski, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.25/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.25/0.54  thf('8', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.25/0.54          | (r2_hidden @ X0 @ X2)
% 0.25/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.25/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.25/0.54  thf('9', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.54         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.25/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.25/0.54  thf('10', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.25/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.25/0.54  thf(t71_relat_1, axiom,
% 0.25/0.54    (![A:$i]:
% 0.25/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.25/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.25/0.54  thf('11', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.25/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.25/0.54  thf(t23_funct_1, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.25/0.54       ( ![C:$i]:
% 0.25/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.25/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.25/0.54               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.25/0.54  thf('12', plain,
% 0.25/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.25/0.54         (~ (v1_relat_1 @ X16)
% 0.25/0.54          | ~ (v1_funct_1 @ X16)
% 0.25/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X17 @ X16) @ X18)
% 0.25/0.54              = (k1_funct_1 @ X16 @ (k1_funct_1 @ X17 @ X18)))
% 0.25/0.54          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X17))
% 0.25/0.54          | ~ (v1_funct_1 @ X17)
% 0.25/0.54          | ~ (v1_relat_1 @ X17))),
% 0.25/0.54      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.25/0.54  thf('13', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.54         (~ (r2_hidden @ X1 @ X0)
% 0.25/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.25/0.54          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.25/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.25/0.54              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.25/0.54          | ~ (v1_funct_1 @ X2)
% 0.25/0.54          | ~ (v1_relat_1 @ X2))),
% 0.25/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.25/0.54  thf(fc3_funct_1, axiom,
% 0.25/0.54    (![A:$i]:
% 0.25/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.25/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.25/0.54  thf('14', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.25/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.25/0.54  thf('15', plain, (![X15 : $i]: (v1_funct_1 @ (k6_relat_1 @ X15))),
% 0.25/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.25/0.54  thf('16', plain,
% 0.25/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.54         (~ (r2_hidden @ X1 @ X0)
% 0.25/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.25/0.54              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.25/0.54          | ~ (v1_funct_1 @ X2)
% 0.25/0.54          | ~ (v1_relat_1 @ X2))),
% 0.25/0.54      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.25/0.54  thf('17', plain,
% 0.25/0.54      (![X0 : $i]:
% 0.25/0.54         (~ (v1_relat_1 @ X0)
% 0.25/0.54          | ~ (v1_funct_1 @ X0)
% 0.25/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.25/0.54              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.25/0.54      inference('sup-', [status(thm)], ['10', '16'])).
% 0.25/0.54  thf('18', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.25/0.54      inference('sup-', [status(thm)], ['6', '9'])).
% 0.25/0.54  thf(t35_funct_1, axiom,
% 0.25/0.54    (![A:$i,B:$i]:
% 0.25/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.25/0.54       ( ( k1_funct_1 @ ( k6_relat_1 @ B ) @ A ) = ( A ) ) ))).
% 0.25/0.54  thf('19', plain,
% 0.25/0.54      (![X19 : $i, X20 : $i]:
% 0.25/0.54         (((k1_funct_1 @ (k6_relat_1 @ X20) @ X19) = (X19))
% 0.25/0.54          | ~ (r2_hidden @ X19 @ X20))),
% 0.25/0.54      inference('cnf', [status(esa)], [t35_funct_1])).
% 0.25/0.54  thf('20', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.25/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.25/0.54  thf('21', plain,
% 0.25/0.54      (![X0 : $i]:
% 0.25/0.54         (~ (v1_relat_1 @ X0)
% 0.25/0.54          | ~ (v1_funct_1 @ X0)
% 0.25/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.25/0.54              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.25/0.54      inference('demod', [status(thm)], ['17', '20'])).
% 0.25/0.54  thf('22', plain,
% 0.25/0.54      (((k1_funct_1 @ sk_C_1 @ sk_A)
% 0.25/0.54         != (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C_1) @ sk_A))),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('23', plain,
% 0.25/0.54      ((((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))
% 0.25/0.54        | ~ (v1_funct_1 @ sk_C_1)
% 0.25/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.25/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.54  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.25/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.54  thf('26', plain,
% 0.25/0.54      (((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 0.25/0.54      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.25/0.54  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.25/0.54  
% 0.25/0.54  % SZS output end Refutation
% 0.25/0.54  
% 0.25/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
