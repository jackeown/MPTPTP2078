%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KInoedmtKB

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  45 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  238 ( 318 expanded)
%              Number of equality atoms :   21 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('0',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_tarski @ X19 @ X18 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) @ X26 )
        = ( k3_xboole_0 @ X24 @ ( k10_relat_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('14',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k10_relat_1 @ sk_A @ sk_C )
     != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KInoedmtKB
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 84 iterations in 0.037s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(t175_funct_2, conjecture,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ![B:$i,C:$i]:
% 0.22/0.53         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.53           ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.53             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i]:
% 0.22/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53          ( ![B:$i,C:$i]:
% 0.22/0.53            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.22/0.53              ( ( k10_relat_1 @ A @ C ) =
% 0.22/0.53                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.22/0.53  thf('0', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t85_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X15 @ X16)
% 0.22/0.53          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.53  thf(t83_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X12 : $i, X13 : $i]:
% 0.22/0.53         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.22/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.22/0.53           (k4_xboole_0 @ X0 @ sk_B)) = (k10_relat_1 @ sk_A @ sk_C))),
% 0.22/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.53  thf(t48_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      (![X10 : $i, X11 : $i]:
% 0.22/0.53         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.53           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.53         = (k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B))),
% 0.22/0.53      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf(commutativity_k2_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X18 : $i, X19 : $i]:
% 0.22/0.53         ((k2_tarski @ X19 @ X18) = (k2_tarski @ X18 @ X19))),
% 0.22/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.53  thf(t12_setfam_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (![X22 : $i, X23 : $i]:
% 0.22/0.53         ((k1_setfam_1 @ (k2_tarski @ X22 @ X23)) = (k3_xboole_0 @ X22 @ X23))),
% 0.22/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.53      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.53         = (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('demod', [status(thm)], ['6', '11'])).
% 0.22/0.53  thf(t139_funct_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ C ) =>
% 0.22/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.22/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.53         (((k10_relat_1 @ (k7_relat_1 @ X25 @ X24) @ X26)
% 0.22/0.53            = (k3_xboole_0 @ X24 @ (k10_relat_1 @ X25 @ X26)))
% 0.22/0.53          | ~ (v1_relat_1 @ X25))),
% 0.22/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.53         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      ((((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.53          != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.22/0.53        | ~ (v1_relat_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      (((k10_relat_1 @ sk_A @ sk_C)
% 0.22/0.53         != (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))),
% 0.22/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.53  thf('18', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['12', '17'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
