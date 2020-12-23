%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJKIsCNfdN

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:38 EST 2020

% Result     : Theorem 50.43s
% Output     : Refutation 50.43s
% Verified   : 
% Statistics : Number of formulae       :   57 (  66 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  443 ( 543 expanded)
%              Number of equality atoms :   29 (  32 expanded)
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k6_subset_1 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 )
      | ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k9_relat_1 @ X18 @ X17 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k6_subset_1 @ X15 @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

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

thf('27',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cJKIsCNfdN
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 50.43/50.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 50.43/50.68  % Solved by: fo/fo7.sh
% 50.43/50.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 50.43/50.68  % done 29981 iterations in 50.226s
% 50.43/50.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 50.43/50.68  % SZS output start Refutation
% 50.43/50.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 50.43/50.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 50.43/50.68  thf(sk_A_type, type, sk_A: $i).
% 50.43/50.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 50.43/50.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 50.43/50.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 50.43/50.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 50.43/50.68  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 50.43/50.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 50.43/50.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 50.43/50.68  thf(sk_B_type, type, sk_B: $i).
% 50.43/50.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 50.43/50.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 50.43/50.68  thf(t123_funct_1, axiom,
% 50.43/50.68    (![A:$i,B:$i,C:$i]:
% 50.43/50.68     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 50.43/50.68       ( ( v2_funct_1 @ C ) =>
% 50.43/50.68         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 50.43/50.68           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 50.43/50.68  thf('0', plain,
% 50.43/50.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 50.43/50.68         (~ (v2_funct_1 @ X24)
% 50.43/50.68          | ((k9_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 50.43/50.68              = (k6_subset_1 @ (k9_relat_1 @ X24 @ X25) @ 
% 50.43/50.68                 (k9_relat_1 @ X24 @ X26)))
% 50.43/50.68          | ~ (v1_funct_1 @ X24)
% 50.43/50.68          | ~ (v1_relat_1 @ X24))),
% 50.43/50.68      inference('cnf', [status(esa)], [t123_funct_1])).
% 50.43/50.68  thf(t145_funct_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 50.43/50.68       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 50.43/50.68  thf('1', plain,
% 50.43/50.68      (![X27 : $i, X28 : $i]:
% 50.43/50.68         ((r1_tarski @ (k9_relat_1 @ X27 @ (k10_relat_1 @ X27 @ X28)) @ X28)
% 50.43/50.68          | ~ (v1_funct_1 @ X27)
% 50.43/50.68          | ~ (v1_relat_1 @ X27))),
% 50.43/50.68      inference('cnf', [status(esa)], [t145_funct_1])).
% 50.43/50.68  thf(l32_xboole_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 50.43/50.68  thf('2', plain,
% 50.43/50.68      (![X3 : $i, X5 : $i]:
% 50.43/50.68         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 50.43/50.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 50.43/50.68  thf(redefinition_k6_subset_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 50.43/50.68  thf('3', plain,
% 50.43/50.68      (![X15 : $i, X16 : $i]:
% 50.43/50.68         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 50.43/50.68      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 50.43/50.68  thf('4', plain,
% 50.43/50.68      (![X3 : $i, X5 : $i]:
% 50.43/50.68         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 50.43/50.68      inference('demod', [status(thm)], ['2', '3'])).
% 50.43/50.68  thf('5', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (~ (v1_relat_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 50.43/50.68              = (k1_xboole_0)))),
% 50.43/50.68      inference('sup-', [status(thm)], ['1', '4'])).
% 50.43/50.68  thf('6', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (((k9_relat_1 @ X1 @ 
% 50.43/50.68            (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 50.43/50.68            = (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v2_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_relat_1 @ X1))),
% 50.43/50.68      inference('sup+', [status(thm)], ['0', '5'])).
% 50.43/50.68  thf('7', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (~ (v2_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_relat_1 @ X1)
% 50.43/50.68          | ((k9_relat_1 @ X1 @ 
% 50.43/50.68              (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 50.43/50.68              = (k1_xboole_0)))),
% 50.43/50.68      inference('simplify', [status(thm)], ['6'])).
% 50.43/50.68  thf(t167_relat_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( v1_relat_1 @ B ) =>
% 50.43/50.68       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 50.43/50.68  thf('8', plain,
% 50.43/50.68      (![X19 : $i, X20 : $i]:
% 50.43/50.68         ((r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k1_relat_1 @ X19))
% 50.43/50.68          | ~ (v1_relat_1 @ X19))),
% 50.43/50.68      inference('cnf', [status(esa)], [t167_relat_1])).
% 50.43/50.68  thf(t36_xboole_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 50.43/50.68  thf('9', plain,
% 50.43/50.68      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 50.43/50.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 50.43/50.68  thf('10', plain,
% 50.43/50.68      (![X15 : $i, X16 : $i]:
% 50.43/50.68         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 50.43/50.68      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 50.43/50.68  thf('11', plain,
% 50.43/50.68      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 50.43/50.68      inference('demod', [status(thm)], ['9', '10'])).
% 50.43/50.68  thf(t12_xboole_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 50.43/50.68  thf('12', plain,
% 50.43/50.68      (![X9 : $i, X10 : $i]:
% 50.43/50.68         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 50.43/50.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 50.43/50.68  thf('13', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         ((k2_xboole_0 @ (k6_subset_1 @ X0 @ X1) @ X0) = (X0))),
% 50.43/50.68      inference('sup-', [status(thm)], ['11', '12'])).
% 50.43/50.68  thf(t11_xboole_1, axiom,
% 50.43/50.68    (![A:$i,B:$i,C:$i]:
% 50.43/50.68     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 50.43/50.68  thf('14', plain,
% 50.43/50.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 50.43/50.68         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 50.43/50.68      inference('cnf', [status(esa)], [t11_xboole_1])).
% 50.43/50.68  thf('15', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.43/50.68         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k6_subset_1 @ X0 @ X2) @ X1))),
% 50.43/50.68      inference('sup-', [status(thm)], ['13', '14'])).
% 50.43/50.68  thf('16', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.43/50.68         (~ (v1_relat_1 @ X0)
% 50.43/50.68          | (r1_tarski @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 50.43/50.68             (k1_relat_1 @ X0)))),
% 50.43/50.68      inference('sup-', [status(thm)], ['8', '15'])).
% 50.43/50.68  thf(t152_relat_1, axiom,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( v1_relat_1 @ B ) =>
% 50.43/50.68       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 50.43/50.68            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 50.43/50.68            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 50.43/50.68  thf('17', plain,
% 50.43/50.68      (![X17 : $i, X18 : $i]:
% 50.43/50.68         (((X17) = (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X18)
% 50.43/50.68          | ~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 50.43/50.68          | ((k9_relat_1 @ X18 @ X17) != (k1_xboole_0)))),
% 50.43/50.68      inference('cnf', [status(esa)], [t152_relat_1])).
% 50.43/50.68  thf('18', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.43/50.68         (~ (v1_relat_1 @ X0)
% 50.43/50.68          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 50.43/50.68              != (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X0)
% 50.43/50.68          | ((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 50.43/50.68      inference('sup-', [status(thm)], ['16', '17'])).
% 50.43/50.68  thf('19', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 50.43/50.68         (((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0))
% 50.43/50.68          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 50.43/50.68              != (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X0))),
% 50.43/50.68      inference('simplify', [status(thm)], ['18'])).
% 50.43/50.68  thf('20', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (((k1_xboole_0) != (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v2_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_relat_1 @ X1)
% 50.43/50.68          | ((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 50.43/50.68              = (k1_xboole_0)))),
% 50.43/50.68      inference('sup-', [status(thm)], ['7', '19'])).
% 50.43/50.68  thf('21', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 50.43/50.68            = (k1_xboole_0))
% 50.43/50.68          | ~ (v2_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_relat_1 @ X1))),
% 50.43/50.68      inference('simplify', [status(thm)], ['20'])).
% 50.43/50.68  thf('22', plain,
% 50.43/50.68      (![X3 : $i, X4 : $i]:
% 50.43/50.68         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 50.43/50.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 50.43/50.68  thf('23', plain,
% 50.43/50.68      (![X15 : $i, X16 : $i]:
% 50.43/50.68         ((k6_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))),
% 50.43/50.68      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 50.43/50.68  thf('24', plain,
% 50.43/50.68      (![X3 : $i, X4 : $i]:
% 50.43/50.68         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 50.43/50.68      inference('demod', [status(thm)], ['22', '23'])).
% 50.43/50.68  thf('25', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         (((k1_xboole_0) != (k1_xboole_0))
% 50.43/50.68          | ~ (v1_relat_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v2_funct_1 @ X1)
% 50.43/50.68          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 50.43/50.68      inference('sup-', [status(thm)], ['21', '24'])).
% 50.43/50.68  thf('26', plain,
% 50.43/50.68      (![X0 : $i, X1 : $i]:
% 50.43/50.68         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 50.43/50.68          | ~ (v2_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_funct_1 @ X1)
% 50.43/50.68          | ~ (v1_relat_1 @ X1))),
% 50.43/50.68      inference('simplify', [status(thm)], ['25'])).
% 50.43/50.68  thf(t152_funct_1, conjecture,
% 50.43/50.68    (![A:$i,B:$i]:
% 50.43/50.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 50.43/50.68       ( ( v2_funct_1 @ B ) =>
% 50.43/50.68         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 50.43/50.68  thf(zf_stmt_0, negated_conjecture,
% 50.43/50.68    (~( ![A:$i,B:$i]:
% 50.43/50.68        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 50.43/50.68          ( ( v2_funct_1 @ B ) =>
% 50.43/50.68            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 50.43/50.68    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 50.43/50.68  thf('27', plain,
% 50.43/50.68      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 50.43/50.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.43/50.68  thf('28', plain,
% 50.43/50.68      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 50.43/50.68      inference('sup-', [status(thm)], ['26', '27'])).
% 50.43/50.68  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 50.43/50.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.43/50.68  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 50.43/50.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.43/50.68  thf('31', plain, ((v2_funct_1 @ sk_B)),
% 50.43/50.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 50.43/50.68  thf('32', plain, ($false),
% 50.43/50.68      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 50.43/50.68  
% 50.43/50.68  % SZS output end Refutation
% 50.43/50.68  
% 50.43/50.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
