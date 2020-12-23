%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.32pwF3bpNk

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:04 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   44 (  60 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  290 ( 509 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

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

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k9_relat_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k9_relat_1 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X13 @ X14 ) @ ( k9_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20','21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.32pwF3bpNk
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:01:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 211 iterations in 0.268s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.56/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.56/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.73  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.56/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.56/0.73  thf(t3_xboole_0, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.56/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.56/0.73            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.56/0.73  thf('0', plain,
% 0.56/0.73      (![X3 : $i, X4 : $i]:
% 0.56/0.73         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.56/0.73      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.56/0.73  thf(t125_funct_1, conjecture,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.73       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.56/0.73         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.73        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.73          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.56/0.73            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.56/0.73  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(d7_xboole_0, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.56/0.73       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.56/0.73  thf('2', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]:
% 0.56/0.73         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.56/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.73  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.73  thf(t4_xboole_0, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.56/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.56/0.73            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.56/0.73  thf('4', plain,
% 0.56/0.73      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.56/0.73          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.56/0.73      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.56/0.73  thf('5', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['3', '4'])).
% 0.56/0.73  thf('6', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.56/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.56/0.73  thf('8', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.56/0.73      inference('sup-', [status(thm)], ['0', '7'])).
% 0.56/0.73  thf(t151_relat_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( v1_relat_1 @ B ) =>
% 0.56/0.73       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.56/0.73         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.56/0.73  thf('9', plain,
% 0.56/0.73      (![X11 : $i, X12 : $i]:
% 0.56/0.73         (~ (r1_xboole_0 @ (k1_relat_1 @ X11) @ X12)
% 0.56/0.73          | ((k9_relat_1 @ X11 @ X12) = (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ X11))),
% 0.56/0.73      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.56/0.73  thf('10', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (v1_relat_1 @ X0)
% 0.56/0.73          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.73  thf('11', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.73  thf(t121_funct_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.56/0.73       ( ( v2_funct_1 @ C ) =>
% 0.56/0.73         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.56/0.73           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.56/0.73  thf('12', plain,
% 0.56/0.73      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.56/0.73         (~ (v2_funct_1 @ X13)
% 0.56/0.73          | ((k9_relat_1 @ X13 @ (k3_xboole_0 @ X14 @ X15))
% 0.56/0.73              = (k3_xboole_0 @ (k9_relat_1 @ X13 @ X14) @ 
% 0.56/0.73                 (k9_relat_1 @ X13 @ X15)))
% 0.56/0.73          | ~ (v1_funct_1 @ X13)
% 0.56/0.73          | ~ (v1_relat_1 @ X13))),
% 0.56/0.73      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.56/0.73  thf('13', plain,
% 0.56/0.73      (![X0 : $i, X2 : $i]:
% 0.56/0.73         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.56/0.73      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.56/0.73  thf('14', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.73         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ X2)
% 0.56/0.73          | ~ (v1_funct_1 @ X2)
% 0.56/0.73          | ~ (v2_funct_1 @ X2)
% 0.56/0.73          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.73  thf('15', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.56/0.73          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.56/0.73          | ~ (v2_funct_1 @ X0)
% 0.56/0.73          | ~ (v1_funct_1 @ X0)
% 0.56/0.73          | ~ (v1_relat_1 @ X0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['11', '14'])).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (((k1_xboole_0) != (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ X0)
% 0.56/0.73          | ~ (v1_relat_1 @ X0)
% 0.56/0.73          | ~ (v1_funct_1 @ X0)
% 0.56/0.73          | ~ (v2_funct_1 @ X0)
% 0.56/0.73          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['10', '15'])).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.56/0.73          | ~ (v2_funct_1 @ X0)
% 0.56/0.73          | ~ (v1_funct_1 @ X0)
% 0.56/0.73          | ~ (v1_relat_1 @ X0))),
% 0.56/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.56/0.73  thf('18', plain,
% 0.56/0.73      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.56/0.73          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('19', plain,
% 0.56/0.73      ((~ (v1_relat_1 @ sk_C_2)
% 0.56/0.73        | ~ (v1_funct_1 @ sk_C_2)
% 0.56/0.73        | ~ (v2_funct_1 @ sk_C_2))),
% 0.56/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.56/0.73  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('21', plain, ((v1_funct_1 @ sk_C_2)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('22', plain, ((v2_funct_1 @ sk_C_2)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('23', plain, ($false),
% 0.56/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.56/0.73  
% 0.56/0.73  % SZS output end Refutation
% 0.56/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
