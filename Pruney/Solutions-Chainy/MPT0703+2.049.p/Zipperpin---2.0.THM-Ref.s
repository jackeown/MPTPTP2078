%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pM0ddHfIxS

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  279 ( 547 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = ( k3_xboole_0 @ X9 @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k9_relat_1 @ X8 @ X6 ) @ ( k9_relat_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','11','12','13','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k10_relat_1 @ X10 @ X9 ) )
        = ( k3_xboole_0 @ X9 @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pM0ddHfIxS
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 18 iterations in 0.015s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.46  thf(t158_funct_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.46           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.46         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.46          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.21/0.46              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.21/0.46            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.21/0.46  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t146_relat_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ A ) =>
% 0.21/0.46       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X5 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.21/0.46          | ~ (v1_relat_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.21/0.46  thf(t148_funct_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.46       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.21/0.46         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9))
% 0.21/0.46            = (k3_xboole_0 @ X9 @ (k9_relat_1 @ X10 @ (k1_relat_1 @ X10))))
% 0.21/0.46          | ~ (v1_funct_1 @ X10)
% 0.21/0.46          | ~ (v1_relat_1 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.46            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ~ (v1_funct_1 @ X0))),
% 0.21/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]:
% 0.21/0.46         (~ (v1_funct_1 @ X0)
% 0.21/0.46          | ~ (v1_relat_1 @ X0)
% 0.21/0.46          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.46              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.21/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t156_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ C ) =>
% 0.21/0.46       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.46         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X6 @ X7)
% 0.21/0.46          | ~ (v1_relat_1 @ X8)
% 0.21/0.46          | (r1_tarski @ (k9_relat_1 @ X8 @ X6) @ (k9_relat_1 @ X8 @ X7)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.21/0.46           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.21/0.46          | ~ (v1_relat_1 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ 
% 0.21/0.46         (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup+', [status(thm)], ['4', '7'])).
% 0.21/0.46  thf('9', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t28_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.46  thf('10', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.46  thf('11', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((r1_tarski @ sk_A @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '11', '12', '13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X9 : $i, X10 : $i]:
% 0.21/0.46         (((k9_relat_1 @ X10 @ (k10_relat_1 @ X10 @ X9))
% 0.21/0.46            = (k3_xboole_0 @ X9 @ (k9_relat_1 @ X10 @ (k1_relat_1 @ X10))))
% 0.21/0.46          | ~ (v1_funct_1 @ X10)
% 0.21/0.46          | ~ (v1_relat_1 @ X10))),
% 0.21/0.46      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.21/0.46  thf(t18_xboole_1, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i]:
% 0.21/0.46     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r1_tarski @ X2 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)))
% 0.21/0.46          | ~ (v1_relat_1 @ X1)
% 0.21/0.46          | ~ (v1_funct_1 @ X1)
% 0.21/0.46          | (r1_tarski @ X2 @ X0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain,
% 0.21/0.46      (((r1_tarski @ sk_A @ sk_B)
% 0.21/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.46  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('22', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.46      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.46  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
