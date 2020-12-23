%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVLJ0MknkD

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:50 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   64 (  91 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  440 ( 827 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k9_relat_1 @ X39 @ ( k10_relat_1 @ X39 @ X38 ) )
        = ( k3_xboole_0 @ X38 @ ( k9_relat_1 @ X39 @ ( k1_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X26: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('11',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','9','10','11'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('13',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X34 @ ( k10_relat_1 @ X34 @ X35 ) ) @ X35 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X28: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X29: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k9_relat_1 @ X39 @ ( k10_relat_1 @ X39 @ X38 ) )
        = ( k3_xboole_0 @ X38 @ ( k9_relat_1 @ X39 @ ( k1_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('23',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C_1 @ sk_A ) @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k9_relat_1 @ X17 @ X15 ) @ ( k9_relat_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k9_relat_1 @ sk_C_1 @ ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','29','30','31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['21','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['17','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sVLJ0MknkD
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.03/2.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.03/2.26  % Solved by: fo/fo7.sh
% 2.03/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.26  % done 3214 iterations in 1.813s
% 2.03/2.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.03/2.26  % SZS output start Refutation
% 2.03/2.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.03/2.26  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.03/2.26  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.03/2.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.03/2.26  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.03/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.03/2.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.03/2.26  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.03/2.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.03/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.03/2.26  thf(t158_funct_1, conjecture,
% 2.03/2.26    (![A:$i,B:$i,C:$i]:
% 2.03/2.26     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.03/2.26       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 2.03/2.26           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 2.03/2.26         ( r1_tarski @ A @ B ) ) ))).
% 2.03/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.26    (~( ![A:$i,B:$i,C:$i]:
% 2.03/2.26        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.03/2.26          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 2.03/2.26              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 2.03/2.26            ( r1_tarski @ A @ B ) ) ) )),
% 2.03/2.26    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 2.03/2.26  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf(t71_relat_1, axiom,
% 2.03/2.26    (![A:$i]:
% 2.03/2.26     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.03/2.26       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.03/2.26  thf('1', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 2.03/2.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.03/2.26  thf(t148_funct_1, axiom,
% 2.03/2.26    (![A:$i,B:$i]:
% 2.03/2.26     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.03/2.26       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 2.03/2.26         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 2.03/2.26  thf('2', plain,
% 2.03/2.26      (![X38 : $i, X39 : $i]:
% 2.03/2.26         (((k9_relat_1 @ X39 @ (k10_relat_1 @ X39 @ X38))
% 2.03/2.26            = (k3_xboole_0 @ X38 @ (k9_relat_1 @ X39 @ (k1_relat_1 @ X39))))
% 2.03/2.26          | ~ (v1_funct_1 @ X39)
% 2.03/2.26          | ~ (v1_relat_1 @ X39))),
% 2.03/2.26      inference('cnf', [status(esa)], [t148_funct_1])).
% 2.03/2.26  thf('3', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         (((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.03/2.26            (k10_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 2.03/2.26            = (k3_xboole_0 @ X1 @ (k9_relat_1 @ (k6_relat_1 @ X0) @ X0)))
% 2.03/2.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.03/2.26          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 2.03/2.26      inference('sup+', [status(thm)], ['1', '2'])).
% 2.03/2.26  thf('4', plain, (![X26 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X26)) = (X26))),
% 2.03/2.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.03/2.26  thf(t146_relat_1, axiom,
% 2.03/2.26    (![A:$i]:
% 2.03/2.26     ( ( v1_relat_1 @ A ) =>
% 2.03/2.26       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 2.03/2.26  thf('5', plain,
% 2.03/2.26      (![X14 : $i]:
% 2.03/2.26         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 2.03/2.26          | ~ (v1_relat_1 @ X14))),
% 2.03/2.26      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.03/2.26  thf('6', plain,
% 2.03/2.26      (![X0 : $i]:
% 2.03/2.26         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 2.03/2.26            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 2.03/2.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 2.03/2.26      inference('sup+', [status(thm)], ['4', '5'])).
% 2.03/2.26  thf('7', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 2.03/2.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.03/2.26  thf(fc3_funct_1, axiom,
% 2.03/2.26    (![A:$i]:
% 2.03/2.26     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.03/2.26       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.03/2.26  thf('8', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 2.03/2.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.03/2.26  thf('9', plain, (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 2.03/2.26      inference('demod', [status(thm)], ['6', '7', '8'])).
% 2.03/2.26  thf('10', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 2.03/2.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.03/2.26  thf('11', plain, (![X29 : $i]: (v1_funct_1 @ (k6_relat_1 @ X29))),
% 2.03/2.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.03/2.26  thf('12', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 2.03/2.26           (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (k3_xboole_0 @ X1 @ X0))),
% 2.03/2.26      inference('demod', [status(thm)], ['3', '9', '10', '11'])).
% 2.03/2.26  thf(t145_funct_1, axiom,
% 2.03/2.26    (![A:$i,B:$i]:
% 2.03/2.26     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.03/2.26       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.03/2.26  thf('13', plain,
% 2.03/2.26      (![X34 : $i, X35 : $i]:
% 2.03/2.26         ((r1_tarski @ (k9_relat_1 @ X34 @ (k10_relat_1 @ X34 @ X35)) @ X35)
% 2.03/2.26          | ~ (v1_funct_1 @ X34)
% 2.03/2.26          | ~ (v1_relat_1 @ X34))),
% 2.03/2.26      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.03/2.26  thf('14', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 2.03/2.26          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 2.03/2.26          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 2.03/2.26      inference('sup+', [status(thm)], ['12', '13'])).
% 2.03/2.26  thf('15', plain, (![X28 : $i]: (v1_relat_1 @ (k6_relat_1 @ X28))),
% 2.03/2.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.03/2.26  thf('16', plain, (![X29 : $i]: (v1_funct_1 @ (k6_relat_1 @ X29))),
% 2.03/2.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 2.03/2.26  thf('17', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.03/2.26      inference('demod', [status(thm)], ['14', '15', '16'])).
% 2.03/2.26  thf('18', plain,
% 2.03/2.26      (![X14 : $i]:
% 2.03/2.26         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 2.03/2.26          | ~ (v1_relat_1 @ X14))),
% 2.03/2.26      inference('cnf', [status(esa)], [t146_relat_1])).
% 2.03/2.26  thf('19', plain,
% 2.03/2.26      (![X38 : $i, X39 : $i]:
% 2.03/2.26         (((k9_relat_1 @ X39 @ (k10_relat_1 @ X39 @ X38))
% 2.03/2.26            = (k3_xboole_0 @ X38 @ (k9_relat_1 @ X39 @ (k1_relat_1 @ X39))))
% 2.03/2.26          | ~ (v1_funct_1 @ X39)
% 2.03/2.26          | ~ (v1_relat_1 @ X39))),
% 2.03/2.26      inference('cnf', [status(esa)], [t148_funct_1])).
% 2.03/2.26  thf('20', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 2.03/2.26            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 2.03/2.26          | ~ (v1_relat_1 @ X0)
% 2.03/2.26          | ~ (v1_relat_1 @ X0)
% 2.03/2.26          | ~ (v1_funct_1 @ X0))),
% 2.03/2.26      inference('sup+', [status(thm)], ['18', '19'])).
% 2.03/2.26  thf('21', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         (~ (v1_funct_1 @ X0)
% 2.03/2.26          | ~ (v1_relat_1 @ X0)
% 2.03/2.26          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 2.03/2.26              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 2.03/2.26      inference('simplify', [status(thm)], ['20'])).
% 2.03/2.26  thf('22', plain,
% 2.03/2.26      (![X0 : $i, X1 : $i]:
% 2.03/2.26         (~ (v1_funct_1 @ X0)
% 2.03/2.26          | ~ (v1_relat_1 @ X0)
% 2.03/2.26          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 2.03/2.26              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 2.03/2.26      inference('simplify', [status(thm)], ['20'])).
% 2.03/2.26  thf('23', plain,
% 2.03/2.26      ((r1_tarski @ (k10_relat_1 @ sk_C_1 @ sk_A) @ 
% 2.03/2.26        (k10_relat_1 @ sk_C_1 @ sk_B))),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf(t156_relat_1, axiom,
% 2.03/2.26    (![A:$i,B:$i,C:$i]:
% 2.03/2.26     ( ( v1_relat_1 @ C ) =>
% 2.03/2.26       ( ( r1_tarski @ A @ B ) =>
% 2.03/2.26         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 2.03/2.26  thf('24', plain,
% 2.03/2.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.03/2.26         (~ (r1_tarski @ X15 @ X16)
% 2.03/2.26          | ~ (v1_relat_1 @ X17)
% 2.03/2.26          | (r1_tarski @ (k9_relat_1 @ X17 @ X15) @ (k9_relat_1 @ X17 @ X16)))),
% 2.03/2.26      inference('cnf', [status(esa)], [t156_relat_1])).
% 2.03/2.26  thf('25', plain,
% 2.03/2.26      (![X0 : $i]:
% 2.03/2.26         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_A)) @ 
% 2.03/2.26           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C_1 @ sk_B)))
% 2.03/2.26          | ~ (v1_relat_1 @ X0))),
% 2.03/2.26      inference('sup-', [status(thm)], ['23', '24'])).
% 2.03/2.26  thf('26', plain,
% 2.03/2.26      (((r1_tarski @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) @ 
% 2.03/2.26         (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)))
% 2.03/2.26        | ~ (v1_relat_1 @ sk_C_1)
% 2.03/2.26        | ~ (v1_funct_1 @ sk_C_1)
% 2.03/2.26        | ~ (v1_relat_1 @ sk_C_1))),
% 2.03/2.26      inference('sup+', [status(thm)], ['22', '25'])).
% 2.03/2.26  thf('27', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C_1))),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf(t28_xboole_1, axiom,
% 2.03/2.26    (![A:$i,B:$i]:
% 2.03/2.26     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.03/2.26  thf('28', plain,
% 2.03/2.26      (![X8 : $i, X9 : $i]:
% 2.03/2.26         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 2.03/2.26      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.03/2.26  thf('29', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C_1)) = (sk_A))),
% 2.03/2.26      inference('sup-', [status(thm)], ['27', '28'])).
% 2.03/2.26  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf('33', plain,
% 2.03/2.26      ((r1_tarski @ sk_A @ 
% 2.03/2.26        (k9_relat_1 @ sk_C_1 @ (k10_relat_1 @ sk_C_1 @ sk_B)))),
% 2.03/2.26      inference('demod', [status(thm)], ['26', '29', '30', '31', '32'])).
% 2.03/2.26  thf('34', plain,
% 2.03/2.26      (((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)))
% 2.03/2.26        | ~ (v1_relat_1 @ sk_C_1)
% 2.03/2.26        | ~ (v1_funct_1 @ sk_C_1))),
% 2.03/2.26      inference('sup+', [status(thm)], ['21', '33'])).
% 2.03/2.26  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf('36', plain, ((v1_funct_1 @ sk_C_1)),
% 2.03/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.26  thf('37', plain,
% 2.03/2.26      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 2.03/2.26      inference('demod', [status(thm)], ['34', '35', '36'])).
% 2.03/2.26  thf(t1_xboole_1, axiom,
% 2.03/2.26    (![A:$i,B:$i,C:$i]:
% 2.03/2.26     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.03/2.26       ( r1_tarski @ A @ C ) ))).
% 2.03/2.26  thf('38', plain,
% 2.03/2.26      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.03/2.26         (~ (r1_tarski @ X5 @ X6)
% 2.03/2.26          | ~ (r1_tarski @ X6 @ X7)
% 2.03/2.26          | (r1_tarski @ X5 @ X7))),
% 2.03/2.26      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.03/2.26  thf('39', plain,
% 2.03/2.26      (![X0 : $i]:
% 2.03/2.26         ((r1_tarski @ sk_A @ X0)
% 2.03/2.26          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C_1)) @ X0))),
% 2.03/2.26      inference('sup-', [status(thm)], ['37', '38'])).
% 2.03/2.26  thf('40', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.03/2.26      inference('sup-', [status(thm)], ['17', '39'])).
% 2.03/2.26  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 2.03/2.26  
% 2.03/2.26  % SZS output end Refutation
% 2.03/2.26  
% 2.03/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
