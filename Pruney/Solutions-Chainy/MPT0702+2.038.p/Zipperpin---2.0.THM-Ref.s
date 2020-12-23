%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RxBg6vrN5V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   57 (  81 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 ( 818 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( r1_tarski @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r1_tarski @ X11 @ ( k10_relat_1 @ X12 @ ( k9_relat_1 @ X12 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( r1_tarski @ ( k10_relat_1 @ X13 @ ( k9_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t178_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k10_relat_1 @ X10 @ X8 ) @ ( k10_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t178_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) )
    = ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_B ) ) @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RxBg6vrN5V
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:39:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 133 iterations in 0.074s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.35/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(t157_funct_1, conjecture,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.52       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.35/0.52           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.35/0.52         ( r1_tarski @ A @ B ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.35/0.52          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.35/0.52              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.35/0.52            ( r1_tarski @ A @ B ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.35/0.52  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t152_funct_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.52       ( ( v2_funct_1 @ B ) =>
% 0.35/0.52         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i]:
% 0.35/0.52         (~ (v2_funct_1 @ X13)
% 0.35/0.52          | (r1_tarski @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X14)) @ X14)
% 0.35/0.52          | ~ (v1_funct_1 @ X13)
% 0.35/0.52          | ~ (v1_relat_1 @ X13))),
% 0.35/0.52      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t12_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.35/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      (((k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.35/0.52         = (k9_relat_1 @ sk_C @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('5', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t146_funct_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ B ) =>
% 0.35/0.52       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.35/0.52         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (![X11 : $i, X12 : $i]:
% 0.35/0.52         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.35/0.52          | (r1_tarski @ X11 @ (k10_relat_1 @ X12 @ (k9_relat_1 @ X12 @ X11)))
% 0.35/0.52          | ~ (v1_relat_1 @ X12))),
% 0.35/0.52      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.52        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.52  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.35/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X13 : $i, X14 : $i]:
% 0.35/0.52         (~ (v2_funct_1 @ X13)
% 0.35/0.52          | (r1_tarski @ (k10_relat_1 @ X13 @ (k9_relat_1 @ X13 @ X14)) @ X14)
% 0.35/0.52          | ~ (v1_funct_1 @ X13)
% 0.35/0.52          | ~ (v1_relat_1 @ X13))),
% 0.35/0.52      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.35/0.52  thf(d10_xboole_0, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X0 : $i, X2 : $i]:
% 0.35/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (v1_relat_1 @ X1)
% 0.35/0.52          | ~ (v1_funct_1 @ X1)
% 0.35/0.52          | ~ (v2_funct_1 @ X1)
% 0.35/0.52          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 0.35/0.52          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      ((((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))
% 0.35/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.35/0.52  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      (((sk_A) = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.35/0.52      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.35/0.52  thf('18', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.35/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.35/0.52  thf('19', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.35/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.35/0.52  thf(t11_xboole_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.52         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.35/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.52  thf(t178_relat_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ C ) =>
% 0.35/0.52       ( ( r1_tarski @ A @ B ) =>
% 0.35/0.52         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.52         (~ (r1_tarski @ X8 @ X9)
% 0.35/0.52          | ~ (v1_relat_1 @ X10)
% 0.35/0.52          | (r1_tarski @ (k10_relat_1 @ X10 @ X8) @ (k10_relat_1 @ X10 @ X9)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t178_relat_1])).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.52         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.35/0.52           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.35/0.52          | ~ (v1_relat_1 @ X2))),
% 0.35/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((r1_tarski @ sk_A @ 
% 0.35/0.52           (k10_relat_1 @ sk_C @ 
% 0.35/0.52            (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0)))
% 0.35/0.52          | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.52      inference('sup+', [status(thm)], ['17', '23'])).
% 0.35/0.52  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (r1_tarski @ sk_A @ 
% 0.35/0.52          (k10_relat_1 @ sk_C @ (k2_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.52  thf('27', plain,
% 0.35/0.52      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['4', '26'])).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i]:
% 0.35/0.52         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.35/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.52  thf('29', plain,
% 0.35/0.52      (((k2_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.35/0.52         = (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.52  thf('30', plain,
% 0.35/0.52      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.35/0.52         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.35/0.52      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.35/0.52  thf('31', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_B)) @ X0)
% 0.35/0.52          | (r1_tarski @ sk_A @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.52        | (r1_tarski @ sk_A @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['1', '31'])).
% 0.35/0.52  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('35', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('36', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.35/0.52      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.35/0.52  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
