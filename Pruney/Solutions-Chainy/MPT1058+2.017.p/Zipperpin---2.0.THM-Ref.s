%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dc8oXYTyqb

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  236 ( 316 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) @ X41 )
        = ( k3_xboole_0 @ X39 @ ( k10_relat_1 @ X40 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C_1 )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k4_xboole_0 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('9',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ( k10_relat_1 @ sk_A @ sk_C_1 )
 != ( k10_relat_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dc8oXYTyqb
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 201 iterations in 0.070s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(t139_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.51         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.51         (((k10_relat_1 @ (k7_relat_1 @ X40 @ X39) @ X41)
% 0.20/0.51            = (k3_xboole_0 @ X39 @ (k10_relat_1 @ X40 @ X41)))
% 0.20/0.51          | ~ (v1_relat_1 @ X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.20/0.51  thf(t175_funct_2, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.51           ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.51             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51          ( ![B:$i,C:$i]:
% 0.20/0.51            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.20/0.51              ( ( k10_relat_1 @ A @ C ) =
% 0.20/0.51                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.20/0.51         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((((k10_relat_1 @ sk_A @ sk_C_1)
% 0.20/0.51          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('3', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t85_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X23 @ X24)
% 0.20/0.51          | (r1_xboole_0 @ X23 @ (k4_xboole_0 @ X25 @ X24)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.51          (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf(t83_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ 
% 0.20/0.51           (k4_xboole_0 @ X0 @ sk_B)) = (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf(t48_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.20/0.51           = (k3_xboole_0 @ X18 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.20/0.51         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C_1) @ sk_B))),
% 0.20/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf(commutativity_k2_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i]:
% 0.20/0.51         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.51  thf(t12_setfam_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X37 : $i, X38 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X37 : $i, X38 : $i]:
% 0.20/0.51         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.20/0.51      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_A @ sk_C_1)
% 0.20/0.51         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.51  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_A @ sk_C_1) != (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['2', '15', '16'])).
% 0.20/0.51  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
