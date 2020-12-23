%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.So0y7PfqLN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:03 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  332 ( 468 expanded)
%              Number of equality atoms :   20 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k7_relat_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k9_relat_1 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X17 @ X18 ) @ ( k9_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('10',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21','22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.So0y7PfqLN
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:58:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 174 iterations in 0.056s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.50  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.50  thf('0', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.23/0.50      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      (![X3 : $i, X4 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.23/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.23/0.50  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.23/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.50  thf(t187_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ![B:$i]:
% 0.23/0.50         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.23/0.50           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X15 : $i, X16 : $i]:
% 0.23/0.50         (~ (r1_xboole_0 @ X15 @ (k1_relat_1 @ X16))
% 0.23/0.50          | ((k7_relat_1 @ X16 @ X15) = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X16))),
% 0.23/0.50      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (~ (v1_relat_1 @ X0)
% 0.23/0.50          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.50  thf(t148_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X13 : $i, X14 : $i]:
% 0.23/0.50         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.23/0.50          | ~ (v1_relat_1 @ X13))),
% 0.23/0.50      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.23/0.50  thf(t125_funct_1, conjecture,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.50       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.23/0.50         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.50        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.50          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.23/0.50            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.23/0.50  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(d7_xboole_0, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.50       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i]:
% 0.23/0.50         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.50  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf(t121_funct_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.50       ( ( v2_funct_1 @ C ) =>
% 0.23/0.50         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.23/0.50           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.50         (~ (v2_funct_1 @ X17)
% 0.23/0.50          | ((k9_relat_1 @ X17 @ (k3_xboole_0 @ X18 @ X19))
% 0.23/0.50              = (k3_xboole_0 @ (k9_relat_1 @ X17 @ X18) @ 
% 0.23/0.50                 (k9_relat_1 @ X17 @ X19)))
% 0.23/0.50          | ~ (v1_funct_1 @ X17)
% 0.23/0.50          | ~ (v1_relat_1 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      (![X0 : $i, X2 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.23/0.50      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.50         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X2)
% 0.23/0.50          | ~ (v1_funct_1 @ X2)
% 0.23/0.50          | ~ (v2_funct_1 @ X2)
% 0.23/0.50          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '11'])).
% 0.23/0.50  thf('13', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k2_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) != (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '12'])).
% 0.23/0.50  thf('14', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ((k2_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) != (k1_xboole_0)))),
% 0.23/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['4', '14'])).
% 0.23/0.50  thf(t60_relat_1, axiom,
% 0.23/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('16', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.23/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.23/0.50          | ~ (v2_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ~ (v1_relat_1 @ X0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('20', plain,
% 0.23/0.50      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.23/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.50  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('23', plain, ((v2_funct_1 @ sk_C)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('24', plain, ($false),
% 0.23/0.50      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
