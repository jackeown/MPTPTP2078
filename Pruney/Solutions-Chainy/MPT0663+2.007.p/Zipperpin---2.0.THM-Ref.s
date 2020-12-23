%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ugJ43TH3du

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  425 ( 813 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k7_relat_1 @ X15 @ X14 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X14 ) @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ ( k6_relat_1 @ X18 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) ) )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('14',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('15',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) ) )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('24',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ X11 @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','30'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X21 @ X22 ) @ X20 )
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ugJ43TH3du
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:14:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 41 iterations in 0.020s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(t71_funct_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.46         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.46        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.46            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.19/0.46              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(commutativity_k2_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.46  thf(t12_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i]:
% 0.19/0.46         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '5'])).
% 0.19/0.46  thf(t94_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X14 : $i, X15 : $i]:
% 0.19/0.46         (((k7_relat_1 @ X15 @ X14) = (k5_relat_1 @ (k6_relat_1 @ X14) @ X15))
% 0.19/0.46          | ~ (v1_relat_1 @ X15))),
% 0.19/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.46  thf(t43_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.19/0.46       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X18 : $i, X19 : $i]:
% 0.19/0.46         ((k5_relat_1 @ (k6_relat_1 @ X19) @ (k6_relat_1 @ X18))
% 0.19/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.46            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.19/0.46      inference('sup+', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf(fc3_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.46       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.46  thf('10', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf(t86_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.19/0.46         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X12)))
% 0.19/0.46          | (r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X2 @ 
% 0.19/0.46             (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.46          | (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X1))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf(t71_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.46  thf('14', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf('15', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('16', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.19/0.46  thf('18', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '17'])).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '5'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 0.19/0.46           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X12)))
% 0.19/0.46          | (r2_hidden @ X11 @ X12)
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X2 @ 
% 0.19/0.46             (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 0.19/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.19/0.46          | (r2_hidden @ X2 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.46  thf('23', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.46  thf('24', plain, (![X16 : $i]: (v1_relat_1 @ (k6_relat_1 @ X16))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.46  thf('26', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['19', '25'])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X11 @ X12)
% 0.19/0.46          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X13))
% 0.19/0.46          | (r2_hidden @ X11 @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X12)))
% 0.19/0.46          | ~ (v1_relat_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ sk_C)
% 0.19/0.46          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.19/0.46          | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('30', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.19/0.46          | ~ (r2_hidden @ sk_A @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['18', '30'])).
% 0.19/0.46  thf(t70_funct_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.19/0.46         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.46  thf('32', plain,
% 0.19/0.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X20 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X22)))
% 0.19/0.46          | ((k1_funct_1 @ (k7_relat_1 @ X21 @ X22) @ X20)
% 0.19/0.46              = (k1_funct_1 @ X21 @ X20))
% 0.19/0.46          | ~ (v1_funct_1 @ X21)
% 0.19/0.46          | ~ (v1_relat_1 @ X21))),
% 0.19/0.46      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.46        | ((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.46            = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.46  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('36', plain,
% 0.19/0.46      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.46         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.19/0.46  thf('37', plain,
% 0.19/0.46      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.46         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('38', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
