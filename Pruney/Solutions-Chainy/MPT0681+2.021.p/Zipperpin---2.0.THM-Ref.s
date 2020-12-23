%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GSfIMtvvsm

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:05 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :  274 ( 418 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k9_relat_1 @ X15 @ ( k3_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X15 @ X16 ) @ ( k9_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( sk_C @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( sk_C @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12','13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GSfIMtvvsm
% 0.14/0.37  % Computer   : n015.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 09:23:53 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 38 iterations in 0.034s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.51  thf(t125_funct_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.23/0.51         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.23/0.51            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.23/0.51  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t121_funct_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51       ( ( v2_funct_1 @ C ) =>
% 0.23/0.51         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.23/0.51           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.51         (~ (v2_funct_1 @ X15)
% 0.23/0.51          | ((k9_relat_1 @ X15 @ (k3_xboole_0 @ X16 @ X17))
% 0.23/0.51              = (k3_xboole_0 @ (k9_relat_1 @ X15 @ X16) @ 
% 0.23/0.51                 (k9_relat_1 @ X15 @ X17)))
% 0.23/0.51          | ~ (v1_funct_1 @ X15)
% 0.23/0.51          | ~ (v1_relat_1 @ X15))),
% 0.23/0.51      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.23/0.51  thf(t4_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ X0 @ X1)
% 0.23/0.51          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((r2_hidden @ 
% 0.23/0.51           (sk_C @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.23/0.51           (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ X2)
% 0.23/0.51          | ~ (v1_funct_1 @ X2)
% 0.23/0.51          | ~ (v2_funct_1 @ X2)
% 0.23/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.23/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.51  thf(t143_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.23/0.51         ( ?[D:$i]:
% 0.23/0.51           ( ( r2_hidden @ D @ B ) & 
% 0.23/0.51             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.23/0.51             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.23/0.51          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.23/0.51          | ~ (v1_relat_1 @ X14))),
% 0.23/0.51      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0))
% 0.23/0.51          | ~ (v2_funct_1 @ X2)
% 0.23/0.51          | ~ (v1_funct_1 @ X2)
% 0.23/0.51          | ~ (v1_relat_1 @ X2)
% 0.23/0.51          | ~ (v1_relat_1 @ X2)
% 0.23/0.51          | (r2_hidden @ 
% 0.23/0.51             (sk_D @ X2 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.23/0.51              (sk_C @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1))) @ 
% 0.23/0.51             (k3_xboole_0 @ X1 @ X0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((r2_hidden @ 
% 0.23/0.51           (sk_D @ X2 @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.23/0.51            (sk_C @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1))) @ 
% 0.23/0.51           (k3_xboole_0 @ X1 @ X0))
% 0.23/0.51          | ~ (v1_relat_1 @ X2)
% 0.23/0.51          | ~ (v1_funct_1 @ X2)
% 0.23/0.51          | ~ (v2_funct_1 @ X2)
% 0.23/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.23/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.23/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.23/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0))
% 0.23/0.51          | ~ (v2_funct_1 @ X2)
% 0.23/0.51          | ~ (v1_funct_1 @ X2)
% 0.23/0.51          | ~ (v1_relat_1 @ X2)
% 0.23/0.51          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v2_funct_1 @ X0)
% 0.23/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.23/0.51          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      ((~ (v2_funct_1 @ sk_C_1)
% 0.23/0.51        | ~ (v1_funct_1 @ sk_C_1)
% 0.23/0.51        | ~ (v1_relat_1 @ sk_C_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain, ((v2_funct_1 @ sk_C_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('15', plain, ($false),
% 0.23/0.51      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
