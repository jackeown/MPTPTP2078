%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uvLTDPEViG

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :  203 ( 293 expanded)
%              Number of equality atoms :   20 (  30 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(o_1_0_funct_1_type,type,(
    o_1_0_funct_1: $i > $i )).

thf(t26_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X6 @ X7 ) @ X8 )
        = ( k2_wellord1 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t26_wellord1])).

thf(t28_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
        = ( k2_wellord1 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A )
          = ( k2_wellord1 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_wellord1])).

thf('1',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_B @ sk_A ) @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_wellord1 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_A ) )
     != ( k2_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( ( k7_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ B )
         => ( ( k1_funct_1 @ C @ D )
            = ( o_1_0_funct_1 @ A ) ) )
      & ( ( k1_relat_1 @ C )
        = B )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X0 @ X2 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( sk_C @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_relat_1 @ ( k7_relat_1 @ ( sk_C @ X0 @ X2 ) @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( sk_C @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( sk_C @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('13',plain,(
    ! [X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ( k2_wellord1 @ sk_B @ sk_A )
 != ( k2_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','14'])).

thf('16',plain,(
    $false ),
    inference(simplify,[status(thm)],['15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uvLTDPEViG
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:18:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 11 iterations in 0.012s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(o_1_0_funct_1_type, type, o_1_0_funct_1: $i > $i).
% 0.20/0.48  thf(t26_wellord1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ C ) =>
% 0.20/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 0.20/0.48         ( k2_wellord1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (((k2_wellord1 @ (k2_wellord1 @ X6 @ X7) @ X8)
% 0.20/0.48            = (k2_wellord1 @ X6 @ (k3_xboole_0 @ X7 @ X8)))
% 0.20/0.48          | ~ (v1_relat_1 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [t26_wellord1])).
% 0.20/0.48  thf(t28_wellord1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.20/0.48         ( k2_wellord1 @ B @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ B ) =>
% 0.20/0.48          ( ( k2_wellord1 @ ( k2_wellord1 @ B @ A ) @ A ) =
% 0.20/0.48            ( k2_wellord1 @ B @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t28_wellord1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (((k2_wellord1 @ (k2_wellord1 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48         != (k2_wellord1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((((k2_wellord1 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_A))
% 0.20/0.48          != (k2_wellord1 @ sk_B @ sk_A))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t98_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.20/0.48  thf(s3_funct_1__e1_27_1__funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ?[C:$i]:
% 0.20/0.48       ( ( ![D:$i]:
% 0.20/0.48           ( ( r2_hidden @ D @ B ) =>
% 0.20/0.48             ( ( k1_funct_1 @ C @ D ) = ( o_1_0_funct_1 @ A ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ C ) = ( B ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]: ((k1_relat_1 @ (sk_C @ X3 @ X4)) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.20/0.48  thf(t90_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.20/0.48         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.20/0.48            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X0 @ X2) @ X1))
% 0.20/0.48            = (k3_xboole_0 @ X0 @ X1))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X0 @ X2)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf('7', plain, (![X3 : $i, X4 : $i]: (v1_relat_1 @ (sk_C @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((k1_relat_1 @ (k7_relat_1 @ (sk_C @ X0 @ X2) @ X1))
% 0.20/0.48           = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (sk_C @ X1 @ X0))
% 0.20/0.48            = (k3_xboole_0 @ X1 @ (k1_relat_1 @ (sk_C @ X1 @ X0))))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C @ X1 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]: ((k1_relat_1 @ (sk_C @ X3 @ X4)) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]: ((k1_relat_1 @ (sk_C @ X3 @ X4)) = (X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.20/0.48  thf('12', plain, (![X3 : $i, X4 : $i]: (v1_relat_1 @ (sk_C @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.20/0.48  thf('13', plain, (![X1 : $i]: ((X1) = (k3_xboole_0 @ X1 @ X1))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((k2_wellord1 @ sk_B @ sk_A) != (k2_wellord1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '13', '14'])).
% 0.20/0.48  thf('16', plain, ($false), inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
