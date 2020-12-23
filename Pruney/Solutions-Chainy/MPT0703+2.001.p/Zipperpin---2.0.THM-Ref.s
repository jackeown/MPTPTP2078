%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lo9wzqSLeJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   63 (  91 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  400 ( 806 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
        = ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','28'])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Lo9wzqSLeJ
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 705 iterations in 0.287s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.54/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.74  thf(t158_funct_1, conjecture,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.54/0.74           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.54/0.74         ( r1_tarski @ A @ B ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i,B:$i,C:$i]:
% 0.54/0.74        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.54/0.74              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.54/0.74            ( r1_tarski @ A @ B ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.54/0.74  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t137_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.54/0.74       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.54/0.74         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.74         (((k10_relat_1 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.54/0.74            = (k3_xboole_0 @ (k10_relat_1 @ X18 @ X19) @ 
% 0.54/0.74               (k10_relat_1 @ X18 @ X20)))
% 0.54/0.74          | ~ (v1_funct_1 @ X18)
% 0.54/0.74          | ~ (v1_relat_1 @ X18))),
% 0.54/0.74      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t28_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X10 : $i, X11 : $i]:
% 0.54/0.74         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.54/0.74      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.54/0.74         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf(commutativity_k2_tarski, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (![X12 : $i, X13 : $i]:
% 0.54/0.74         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.54/0.74      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.54/0.74  thf(t12_setfam_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.74  thf('6', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (![X16 : $i, X17 : $i]:
% 0.54/0.74         ((k1_setfam_1 @ (k2_tarski @ X16 @ X17)) = (k3_xboole_0 @ X16 @ X17))),
% 0.54/0.74      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.54/0.74  thf('9', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ 
% 0.54/0.74         (k10_relat_1 @ sk_C @ sk_A)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['4', '9'])).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      ((((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.54/0.74          = (k10_relat_1 @ sk_C @ sk_A))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['1', '10'])).
% 0.54/0.74  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.54/0.74         = (k10_relat_1 @ sk_C @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.54/0.74  thf('15', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['7', '8'])).
% 0.54/0.74  thf(t17_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.74  thf('17', plain,
% 0.54/0.74      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.54/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.54/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.74  thf(t12_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      (![X6 : $i, X7 : $i]:
% 0.54/0.74         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.54/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.74  thf('20', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i]:
% 0.54/0.74         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (X0))),
% 0.54/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.74  thf(t11_xboole_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.54/0.74  thf('21', plain,
% 0.54/0.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.74         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.54/0.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.54/0.74  thf('22', plain,
% 0.54/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X1))),
% 0.54/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.74  thf('23', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['15', '22'])).
% 0.54/0.74  thf(t147_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.54/0.74         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.54/0.74  thf('24', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X21 @ (k2_relat_1 @ X22))
% 0.54/0.74          | ((k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X21)) = (X21))
% 0.54/0.74          | ~ (v1_funct_1 @ X22)
% 0.54/0.74          | ~ (v1_relat_1 @ X22))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.54/0.74  thf('25', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (~ (v1_relat_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74          | ((k9_relat_1 @ sk_C @ 
% 0.54/0.74              (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.54/0.74              = (k3_xboole_0 @ X0 @ sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.54/0.74  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('28', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.54/0.74           = (k3_xboole_0 @ X0 @ sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.54/0.74  thf('29', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.54/0.74         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['14', '28'])).
% 0.54/0.74  thf('30', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('31', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i]:
% 0.54/0.74         (~ (r1_tarski @ X21 @ (k2_relat_1 @ X22))
% 0.54/0.74          | ((k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X21)) = (X21))
% 0.54/0.74          | ~ (v1_funct_1 @ X22)
% 0.54/0.74          | ~ (v1_relat_1 @ X22))),
% 0.54/0.74      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.54/0.74  thf('32', plain,
% 0.54/0.74      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('35', plain,
% 0.54/0.74      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.54/0.74      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.54/0.74  thf('36', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['29', '35'])).
% 0.54/0.74  thf('37', plain,
% 0.54/0.74      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.54/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.74  thf('38', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.54/0.74      inference('sup+', [status(thm)], ['36', '37'])).
% 0.54/0.74  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
