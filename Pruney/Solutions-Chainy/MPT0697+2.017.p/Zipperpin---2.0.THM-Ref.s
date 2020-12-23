%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xgMTBd8aNg

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:39 EST 2020

% Result     : Theorem 18.74s
% Output     : Refutation 18.74s
% Verified   : 
% Statistics : Number of formulae       :   53 (  62 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  422 ( 522 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k9_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X24 @ X25 ) @ ( k9_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ ( k10_relat_1 @ X27 @ X28 ) ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X11 @ X12 ) @ X11 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t152_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_1])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['26','27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xgMTBd8aNg
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:52:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 18.74/18.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.74/18.98  % Solved by: fo/fo7.sh
% 18.74/18.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.74/18.98  % done 17302 iterations in 18.487s
% 18.74/18.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.74/18.98  % SZS output start Refutation
% 18.74/18.98  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.74/18.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 18.74/18.98  thf(sk_A_type, type, sk_A: $i).
% 18.74/18.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 18.74/18.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 18.74/18.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.74/18.98  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 18.74/18.98  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 18.74/18.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 18.74/18.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 18.74/18.98  thf(sk_B_type, type, sk_B: $i).
% 18.74/18.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 18.74/18.98  thf(t123_funct_1, axiom,
% 18.74/18.98    (![A:$i,B:$i,C:$i]:
% 18.74/18.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 18.74/18.98       ( ( v2_funct_1 @ C ) =>
% 18.74/18.98         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 18.74/18.98           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 18.74/18.98  thf('0', plain,
% 18.74/18.98      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.74/18.98         (~ (v2_funct_1 @ X24)
% 18.74/18.98          | ((k9_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 18.74/18.98              = (k6_subset_1 @ (k9_relat_1 @ X24 @ X25) @ 
% 18.74/18.98                 (k9_relat_1 @ X24 @ X26)))
% 18.74/18.98          | ~ (v1_funct_1 @ X24)
% 18.74/18.98          | ~ (v1_relat_1 @ X24))),
% 18.74/18.98      inference('cnf', [status(esa)], [t123_funct_1])).
% 18.74/18.98  thf(t145_funct_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]:
% 18.74/18.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.74/18.98       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 18.74/18.98  thf('1', plain,
% 18.74/18.98      (![X27 : $i, X28 : $i]:
% 18.74/18.98         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 18.74/18.98          | ~ (v1_funct_1 @ X27)
% 18.74/18.98          | ~ (v1_relat_1 @ X27))),
% 18.74/18.98      inference('cnf', [status(esa)], [t145_funct_1])).
% 18.74/18.98  thf(l32_xboole_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]:
% 18.74/18.98     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 18.74/18.98  thf('2', plain,
% 18.74/18.98      (![X3 : $i, X5 : $i]:
% 18.74/18.98         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 18.74/18.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 18.74/18.98  thf(redefinition_k6_subset_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 18.74/18.98  thf('3', plain,
% 18.74/18.98      (![X15 : $i, X16 : $i]:
% 18.74/18.98         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.74/18.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.98  thf('4', plain,
% 18.74/18.98      (![X3 : $i, X5 : $i]:
% 18.74/18.98         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 18.74/18.98      inference('demod', [status(thm)], ['2', '3'])).
% 18.74/18.98  thf('5', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (~ (v1_relat_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 18.74/18.98              = (k1_xboole_0)))),
% 18.74/18.98      inference('sup-', [status(thm)], ['1', '4'])).
% 18.74/18.98  thf('6', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (((k9_relat_1 @ X1 @ 
% 18.74/18.98            (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 18.74/18.98            = (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v2_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_relat_1 @ X1))),
% 18.74/18.98      inference('sup+', [status(thm)], ['0', '5'])).
% 18.74/18.98  thf('7', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (~ (v2_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_relat_1 @ X1)
% 18.74/18.98          | ((k9_relat_1 @ X1 @ 
% 18.74/18.98              (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 18.74/18.98              = (k1_xboole_0)))),
% 18.74/18.98      inference('simplify', [status(thm)], ['6'])).
% 18.74/18.98  thf(t167_relat_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]:
% 18.74/18.98     ( ( v1_relat_1 @ B ) =>
% 18.74/18.98       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 18.74/18.98  thf('8', plain,
% 18.74/18.98      (![X19 : $i, X20 : $i]:
% 18.74/18.98         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 18.74/18.98          | ~ (v1_relat_1 @ X19))),
% 18.74/18.98      inference('cnf', [status(esa)], [t167_relat_1])).
% 18.74/18.98  thf(t36_xboole_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 18.74/18.98  thf('9', plain,
% 18.74/18.98      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 18.74/18.98      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.74/18.98  thf('10', plain,
% 18.74/18.98      (![X15 : $i, X16 : $i]:
% 18.74/18.98         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.74/18.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.98  thf('11', plain,
% 18.74/18.98      (![X11 : $i, X12 : $i]: (r1_tarski @ (k6_subset_1 @ X11 @ X12) @ X11)),
% 18.74/18.98      inference('demod', [status(thm)], ['9', '10'])).
% 18.74/18.98  thf(t1_xboole_1, axiom,
% 18.74/18.98    (![A:$i,B:$i,C:$i]:
% 18.74/18.98     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 18.74/18.98       ( r1_tarski @ A @ C ) ))).
% 18.74/18.98  thf('12', plain,
% 18.74/18.98      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.74/18.98         (~ (r1_tarski @ X8 @ X9)
% 18.74/18.98          | ~ (r1_tarski @ X9 @ X10)
% 18.74/18.98          | (r1_tarski @ X8 @ X10))),
% 18.74/18.98      inference('cnf', [status(esa)], [t1_xboole_1])).
% 18.74/18.98  thf('13', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.74/18.98         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 18.74/18.98      inference('sup-', [status(thm)], ['11', '12'])).
% 18.74/18.98  thf('14', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.74/18.98         (~ (v1_relat_1 @ X0)
% 18.74/18.98          | (r1_tarski @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 18.74/18.98             (k1_relat_1 @ X0)))),
% 18.74/18.98      inference('sup-', [status(thm)], ['8', '13'])).
% 18.74/18.98  thf(t152_relat_1, axiom,
% 18.74/18.98    (![A:$i,B:$i]:
% 18.74/18.98     ( ( v1_relat_1 @ B ) =>
% 18.74/18.98       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 18.74/18.98            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 18.74/18.98            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 18.74/18.98  thf('15', plain,
% 18.74/18.98      (![X17 : $i, X18 : $i]:
% 18.74/18.98         (((X17) = (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X18)
% 18.74/18.98          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 18.74/18.98          | ((k9_relat_1 @ X18 @ X17) != (k1_xboole_0)))),
% 18.74/18.98      inference('cnf', [status(esa)], [t152_relat_1])).
% 18.74/18.98  thf('16', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.74/18.98         (~ (v1_relat_1 @ X0)
% 18.74/18.98          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 18.74/18.98              != (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X0)
% 18.74/18.98          | ((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 18.74/18.98      inference('sup-', [status(thm)], ['14', '15'])).
% 18.74/18.98  thf('17', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.74/18.98         (((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0))
% 18.74/18.98          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 18.74/18.98              != (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X0))),
% 18.74/18.98      inference('simplify', [status(thm)], ['16'])).
% 18.74/18.98  thf('18', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (((k1_xboole_0) != (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v2_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_relat_1 @ X1)
% 18.74/18.98          | ((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 18.74/18.98              = (k1_xboole_0)))),
% 18.74/18.98      inference('sup-', [status(thm)], ['7', '17'])).
% 18.74/18.98  thf('19', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 18.74/18.98            = (k1_xboole_0))
% 18.74/18.98          | ~ (v2_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_relat_1 @ X1))),
% 18.74/18.98      inference('simplify', [status(thm)], ['18'])).
% 18.74/18.98  thf('20', plain,
% 18.74/18.98      (![X3 : $i, X4 : $i]:
% 18.74/18.98         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 18.74/18.98      inference('cnf', [status(esa)], [l32_xboole_1])).
% 18.74/18.98  thf('21', plain,
% 18.74/18.98      (![X15 : $i, X16 : $i]:
% 18.74/18.98         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 18.74/18.98      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 18.74/18.98  thf('22', plain,
% 18.74/18.98      (![X3 : $i, X4 : $i]:
% 18.74/18.98         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 18.74/18.98      inference('demod', [status(thm)], ['20', '21'])).
% 18.74/18.98  thf('23', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         (((k1_xboole_0) != (k1_xboole_0))
% 18.74/18.98          | ~ (v1_relat_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v2_funct_1 @ X1)
% 18.74/18.98          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 18.74/18.98      inference('sup-', [status(thm)], ['19', '22'])).
% 18.74/18.98  thf('24', plain,
% 18.74/18.98      (![X0 : $i, X1 : $i]:
% 18.74/18.98         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 18.74/18.98          | ~ (v2_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_funct_1 @ X1)
% 18.74/18.98          | ~ (v1_relat_1 @ X1))),
% 18.74/18.98      inference('simplify', [status(thm)], ['23'])).
% 18.74/18.98  thf(t152_funct_1, conjecture,
% 18.74/18.98    (![A:$i,B:$i]:
% 18.74/18.98     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.74/18.98       ( ( v2_funct_1 @ B ) =>
% 18.74/18.98         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 18.74/18.98  thf(zf_stmt_0, negated_conjecture,
% 18.74/18.98    (~( ![A:$i,B:$i]:
% 18.74/18.98        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 18.74/18.98          ( ( v2_funct_1 @ B ) =>
% 18.74/18.98            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 18.74/18.98    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 18.74/18.98  thf('25', plain,
% 18.74/18.98      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 18.74/18.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.98  thf('26', plain,
% 18.74/18.98      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 18.74/18.98      inference('sup-', [status(thm)], ['24', '25'])).
% 18.74/18.98  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 18.74/18.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.98  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 18.74/18.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.98  thf('29', plain, ((v2_funct_1 @ sk_B)),
% 18.74/18.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.74/18.98  thf('30', plain, ($false),
% 18.74/18.98      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 18.74/18.98  
% 18.74/18.98  % SZS output end Refutation
% 18.74/18.98  
% 18.82/18.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
