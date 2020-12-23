%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rsdxK6oJB

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  304 ( 566 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k9_relat_1 @ X10 @ ( k6_subset_1 @ X11 @ X12 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X10 @ X11 ) @ ( k9_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k6_subset_1 @ X3 @ X5 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k1_relat_1 @ X9 ) )
      | ( ( k9_relat_1 @ X9 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ X0 ) )
       != k1_xboole_0 )
      | ( ( k6_subset_1 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k6_subset_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( k6_subset_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k6_subset_1 @ X6 @ X7 )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1rsdxK6oJB
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 15:54:04 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 39 iterations in 0.049s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.48  thf(t157_funct_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.19/0.48           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.19/0.48         ( r1_tarski @ A @ B ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.19/0.48              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.19/0.48            ( r1_tarski @ A @ B ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.19/0.48  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(l32_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i]:
% 0.19/0.48         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i, X2 : $i]:
% 0.19/0.48         (((k6_subset_1 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (((k6_subset_1 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.19/0.48         = (k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.19/0.48  thf(t123_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48       ( ( v2_funct_1 @ C ) =>
% 0.19/0.48         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.19/0.48           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (v2_funct_1 @ X10)
% 0.19/0.48          | ((k9_relat_1 @ X10 @ (k6_subset_1 @ X11 @ X12))
% 0.19/0.48              = (k6_subset_1 @ (k9_relat_1 @ X10 @ X11) @ 
% 0.19/0.48                 (k9_relat_1 @ X10 @ X12)))
% 0.19/0.48          | ~ (v1_funct_1 @ X10)
% 0.19/0.48          | ~ (v1_relat_1 @ X10))),
% 0.19/0.48      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.48        | ~ (v2_funct_1 @ sk_C))),
% 0.19/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.19/0.48  thf('12', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t109_xboole_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.48         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k6_subset_1 @ X3 @ X5) @ X4))),
% 0.19/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (r1_tarski @ (k6_subset_1 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.48  thf(t152_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.19/0.48            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]:
% 0.19/0.48         (((X8) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X9)
% 0.19/0.48          | ~ (r1_tarski @ X8 @ (k1_relat_1 @ X9))
% 0.19/0.48          | ((k9_relat_1 @ X9 @ X8) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ sk_C)
% 0.19/0.48          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.48  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k9_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ X0)) != (k1_xboole_0))
% 0.19/0.48          | ((k6_subset_1 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.48        | ((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '20'])).
% 0.19/0.48  thf('22', plain, (((k6_subset_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]: ((k6_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.48  thf('27', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.48  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
