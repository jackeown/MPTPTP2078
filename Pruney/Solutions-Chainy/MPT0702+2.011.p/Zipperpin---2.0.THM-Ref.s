%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lzVDTvide

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  428 ( 965 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k9_relat_1 @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X16 @ X17 ) @ ( k9_relat_1 @ X16 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
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
    ( ( k9_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('13',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( r1_tarski @ ( k10_relat_1 @ X21 @ ( k9_relat_1 @ X21 @ X22 ) ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( r1_tarski @ X19 @ ( k10_relat_1 @ X20 @ ( k9_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('41',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1lzVDTvide
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 120 iterations in 0.057s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(t157_funct_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.20/0.51           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.51         ( r1_tarski @ A @ B ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.20/0.51              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.20/0.51            ( r1_tarski @ A @ B ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.20/0.51  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t28_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.20/0.51         = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_B) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.51         = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf(t121_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ C ) =>
% 0.20/0.51         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.51           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X16)
% 0.20/0.51          | ((k9_relat_1 @ X16 @ (k3_xboole_0 @ X17 @ X18))
% 0.20/0.51              = (k3_xboole_0 @ (k9_relat_1 @ X16 @ X17) @ 
% 0.20/0.51                 (k9_relat_1 @ X16 @ X18)))
% 0.20/0.51          | ~ (v1_funct_1 @ X16)
% 0.20/0.51          | ~ (v1_relat_1 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.51          = (k9_relat_1 @ sk_C @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (((k9_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.51         = (k9_relat_1 @ sk_C @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.20/0.51  thf(t152_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ B ) =>
% 0.20/0.51         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X21)
% 0.20/0.51          | (r1_tarski @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X22)) @ X22)
% 0.20/0.51          | ~ (v1_funct_1 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.20/0.51         (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.51        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v2_funct_1 @ sk_C))),
% 0.20/0.51      inference('sup+', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ 
% 0.20/0.51        (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X21)
% 0.20/0.51          | (r1_tarski @ (k10_relat_1 @ X21 @ (k9_relat_1 @ X21 @ X22)) @ X22)
% 0.20/0.51          | ~ (v1_funct_1 @ X21)
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t152_funct_1])).
% 0.20/0.51  thf('19', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t146_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.51         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.20/0.51          | (r1_tarski @ X19 @ (k10_relat_1 @ X20 @ (k9_relat_1 @ X20 @ X19)))
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | (r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i]:
% 0.20/0.51         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.20/0.51        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.51        | ~ (v2_funct_1 @ sk_C)
% 0.20/0.51        | ((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '25'])).
% 0.20/0.51  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain, ((v2_funct_1 @ sk_C)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ sk_A)) = (sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.20/0.51  thf('31', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.51  thf(t48_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.20/0.51           = (k3_xboole_0 @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.20/0.51  thf(t36_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.20/0.51      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.20/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.20/0.51      inference('sup+', [status(thm)], ['32', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X2 : $i, X4 : $i]:
% 0.20/0.51         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.20/0.51          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.20/0.51      inference('sup+', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('41', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
