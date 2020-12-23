%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziM5nW2yvW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 376 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X32 @ X31 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X31 ) @ X32 ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t38_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ C @ A )
          = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k3_xboole_0 @ ( k1_relat_1 @ X34 ) @ X35 ) )
      | ( ( k1_funct_1 @ X34 @ X33 )
        = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X34 ) @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t38_funct_1])).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X34 ) @ X35 ) ) )
      | ( ( k1_funct_1 @ X34 @ X33 )
        = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ X34 ) @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
      = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ziM5nW2yvW
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:13:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 20 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(t94_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      (![X31 : $i, X32 : $i]:
% 0.22/0.48         (((k7_relat_1 @ X32 @ X31) = (k5_relat_1 @ (k6_relat_1 @ X31) @ X32))
% 0.22/0.48          | ~ (v1_relat_1 @ X32))),
% 0.22/0.48      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.22/0.48  thf(t71_funct_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.48       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.22/0.48         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.48          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.22/0.48            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.22/0.48              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t12_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((r2_hidden @ sk_A @ 
% 0.22/0.48        (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.22/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(t38_funct_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.48       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.22/0.48         ( ( k1_funct_1 @ C @ A ) =
% 0.22/0.48           ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ B ) @ C ) @ A ) ) ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X33 @ (k3_xboole_0 @ (k1_relat_1 @ X34) @ X35))
% 0.22/0.48          | ((k1_funct_1 @ X34 @ X33)
% 0.22/0.48              = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X35) @ X34) @ X33))
% 0.22/0.48          | ~ (v1_funct_1 @ X34)
% 0.22/0.48          | ~ (v1_relat_1 @ X34))),
% 0.22/0.48      inference('cnf', [status(esa)], [t38_funct_1])).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X29 : $i, X30 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X33 @ 
% 0.22/0.48             (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X34) @ X35)))
% 0.22/0.48          | ((k1_funct_1 @ X34 @ X33)
% 0.22/0.48              = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X35) @ X34) @ X33))
% 0.22/0.48          | ~ (v1_funct_1 @ X34)
% 0.22/0.48          | ~ (v1_relat_1 @ X34))),
% 0.22/0.48      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.48        | ((k1_funct_1 @ sk_C @ sk_A)
% 0.22/0.48            = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.48  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((k1_funct_1 @ sk_C @ sk_A)
% 0.22/0.48         = (k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_C) @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      ((((k1_funct_1 @ sk_C @ sk_A)
% 0.22/0.48          = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.48      inference('sup+', [status(thm)], ['0', '10'])).
% 0.22/0.48  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (((k1_funct_1 @ sk_C @ sk_A)
% 0.22/0.48         = (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.48         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('15', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
