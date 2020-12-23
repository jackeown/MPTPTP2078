%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7bxlsRFDF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:03 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   31 (  40 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  205 ( 341 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

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

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k9_relat_1 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X4 @ X5 ) @ ( k9_relat_1 @ X4 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('5',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['11','12','13','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.18  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R7bxlsRFDF
% 0.18/0.38  % Computer   : n024.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 18:28:51 EST 2020
% 0.18/0.39  % CPUTime    : 
% 0.18/0.39  % Running portfolio for 600 s
% 0.18/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.39  % Number of cores: 8
% 0.18/0.39  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.25/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.52  % Solved by: fo/fo7.sh
% 0.25/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.52  % done 19 iterations in 0.019s
% 0.25/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.52  % SZS output start Refutation
% 0.25/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.25/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.25/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.25/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.25/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.25/0.52  thf(t149_relat_1, axiom,
% 0.25/0.52    (![A:$i]:
% 0.25/0.52     ( ( v1_relat_1 @ A ) =>
% 0.25/0.52       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.52  thf('0', plain,
% 0.25/0.52      (![X3 : $i]:
% 0.25/0.52         (((k9_relat_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))
% 0.25/0.52          | ~ (v1_relat_1 @ X3))),
% 0.25/0.52      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.25/0.52  thf(t125_funct_1, conjecture,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.52       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.25/0.52         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.25/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.25/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.52          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.25/0.52            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.25/0.52    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.25/0.52  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf(d7_xboole_0, axiom,
% 0.25/0.52    (![A:$i,B:$i]:
% 0.25/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.25/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.25/0.52  thf('2', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i]:
% 0.25/0.52         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.25/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.52  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.52  thf(t121_funct_1, axiom,
% 0.25/0.52    (![A:$i,B:$i,C:$i]:
% 0.25/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.25/0.52       ( ( v2_funct_1 @ C ) =>
% 0.25/0.52         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.25/0.52           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.25/0.52  thf('4', plain,
% 0.25/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.25/0.52         (~ (v2_funct_1 @ X4)
% 0.25/0.52          | ((k9_relat_1 @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.25/0.52              = (k3_xboole_0 @ (k9_relat_1 @ X4 @ X5) @ (k9_relat_1 @ X4 @ X6)))
% 0.25/0.52          | ~ (v1_funct_1 @ X4)
% 0.25/0.52          | ~ (v1_relat_1 @ X4))),
% 0.25/0.52      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.25/0.52  thf('5', plain,
% 0.25/0.52      (![X0 : $i, X2 : $i]:
% 0.25/0.52         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.25/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.25/0.52  thf('6', plain,
% 0.25/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.52         (((k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.25/0.52          | ~ (v1_relat_1 @ X2)
% 0.25/0.52          | ~ (v1_funct_1 @ X2)
% 0.25/0.52          | ~ (v2_funct_1 @ X2)
% 0.25/0.52          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.52  thf('7', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         (((k9_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.25/0.52          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.25/0.52          | ~ (v2_funct_1 @ X0)
% 0.25/0.52          | ~ (v1_funct_1 @ X0)
% 0.25/0.52          | ~ (v1_relat_1 @ X0))),
% 0.25/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.25/0.52  thf('8', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         (((k1_xboole_0) != (k1_xboole_0))
% 0.25/0.52          | ~ (v1_relat_1 @ X0)
% 0.25/0.52          | ~ (v1_relat_1 @ X0)
% 0.25/0.52          | ~ (v1_funct_1 @ X0)
% 0.25/0.52          | ~ (v2_funct_1 @ X0)
% 0.25/0.52          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.25/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.25/0.52  thf('9', plain,
% 0.25/0.52      (![X0 : $i]:
% 0.25/0.52         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.25/0.52          | ~ (v2_funct_1 @ X0)
% 0.25/0.52          | ~ (v1_funct_1 @ X0)
% 0.25/0.52          | ~ (v1_relat_1 @ X0))),
% 0.25/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.25/0.52  thf('10', plain,
% 0.25/0.52      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('11', plain,
% 0.25/0.52      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 0.25/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.25/0.52  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('14', plain, ((v2_funct_1 @ sk_C)),
% 0.25/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.52  thf('15', plain, ($false),
% 0.25/0.52      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.25/0.52  
% 0.25/0.52  % SZS output end Refutation
% 0.25/0.52  
% 0.25/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
