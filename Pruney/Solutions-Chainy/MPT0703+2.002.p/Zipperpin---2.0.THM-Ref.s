%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lbnTddtpOH

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:49 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   59 (  87 expanded)
%              Number of leaves         :   20 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  380 ( 786 expanded)
%              Number of equality atoms :   25 (  34 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

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

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_B ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X14 @ X15 ) @ ( k10_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','10'])).

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
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('16',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
        = ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['14','26'])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k2_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ ( k10_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lbnTddtpOH
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 439 iterations in 0.206s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(t158_funct_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.46/0.65           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.46/0.65         ( r1_tarski @ A @ B ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.46/0.65              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.46/0.65            ( r1_tarski @ A @ B ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.46/0.65  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t28_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.46/0.65         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf(commutativity_k2_tarski, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X10 : $i, X11 : $i]:
% 0.46/0.65         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.46/0.65      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.46/0.65  thf(t12_setfam_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X12 : $i, X13 : $i]:
% 0.46/0.65         ((k1_setfam_1 @ (k2_tarski @ X12 @ X13)) = (k3_xboole_0 @ X12 @ X13))),
% 0.46/0.65      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_B) @ 
% 0.46/0.65         (k10_relat_1 @ sk_C @ sk_A)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['3', '8'])).
% 0.46/0.65  thf(t137_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.65       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.46/0.65         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.65         (((k10_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.46/0.65            = (k3_xboole_0 @ (k10_relat_1 @ X14 @ X15) @ 
% 0.46/0.65               (k10_relat_1 @ X14 @ X16)))
% 0.46/0.65          | ~ (v1_funct_1 @ X14)
% 0.46/0.65          | ~ (v1_relat_1 @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      ((((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.46/0.65          = (k10_relat_1 @ sk_C @ sk_A))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (((k10_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.46/0.65         = (k10_relat_1 @ sk_C @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('16', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t17_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.46/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.65  thf(t1_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ A @ C ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X5 @ X6)
% 0.46/0.65          | ~ (r1_tarski @ X6 @ X7)
% 0.46/0.65          | (r1_tarski @ X5 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['15', '20'])).
% 0.46/0.65  thf(t147_funct_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.46/0.65         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.46/0.65          | ((k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X17)) = (X17))
% 0.46/0.65          | ~ (v1_funct_1 @ X18)
% 0.46/0.65          | ~ (v1_relat_1 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ sk_C)
% 0.46/0.65          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65          | ((k9_relat_1 @ sk_C @ 
% 0.46/0.65              (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.46/0.65              = (k3_xboole_0 @ X0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k3_xboole_0 @ X0 @ sk_A)))
% 0.46/0.65           = (k3_xboole_0 @ X0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A))
% 0.46/0.65         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['14', '26'])).
% 0.46/0.65  thf('28', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X17 @ (k2_relat_1 @ X18))
% 0.46/0.65          | ((k9_relat_1 @ X18 @ (k10_relat_1 @ X18 @ X17)) = (X17))
% 0.46/0.65          | ~ (v1_funct_1 @ X18)
% 0.46/0.65          | ~ (v1_relat_1 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.65  thf('34', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['27', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.46/0.65      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.46/0.65  thf('36', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.46/0.65      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
