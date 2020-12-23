%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbukbQnXdJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  43 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  233 ( 303 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t216_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t216_relat_1])).

thf('0',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t212_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k6_subset_1 @ X9 @ ( k7_relat_1 @ X9 @ X10 ) ) )
        = ( k6_subset_1 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t212_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relat_1 @ ( k4_xboole_0 @ X9 @ ( k7_relat_1 @ X9 @ X10 ) ) )
        = ( k4_xboole_0 @ ( k1_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_xboole_0 @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( ( k7_relat_1 @ X8 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k4_xboole_0 @ X0 @ ( k7_relat_1 @ X0 @ sk_B ) ) @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ( k7_relat_1 @ ( k6_subset_1 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k6_subset_1 @ X3 @ X4 )
      = ( k4_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ( k7_relat_1 @ ( k4_xboole_0 @ sk_C @ ( k7_relat_1 @ sk_C @ sk_B ) ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tbukbQnXdJ
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:12:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 11 iterations in 0.011s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(t216_relat_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ C ) =>
% 0.20/0.45       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45         ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.45           ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ C ) =>
% 0.20/0.45          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45            ( ( k7_relat_1 @ ( k6_subset_1 @ C @ ( k7_relat_1 @ C @ B ) ) @ A ) =
% 0.20/0.45              ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t216_relat_1])).
% 0.20/0.45  thf('0', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t85_xboole_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.45          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X1)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t212_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k1_relat_1 @ ( k6_subset_1 @ B @ ( k7_relat_1 @ B @ A ) ) ) =
% 0.20/0.45         ( k6_subset_1 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k6_subset_1 @ X9 @ (k7_relat_1 @ X9 @ X10)))
% 0.20/0.45            = (k6_subset_1 @ (k1_relat_1 @ X9) @ X10))
% 0.20/0.45          | ~ (v1_relat_1 @ X9))),
% 0.20/0.45      inference('cnf', [status(esa)], [t212_relat_1])).
% 0.20/0.45  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]: ((k6_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]: ((k6_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      (![X9 : $i, X10 : $i]:
% 0.20/0.45         (((k1_relat_1 @ (k4_xboole_0 @ X9 @ (k7_relat_1 @ X9 @ X10)))
% 0.20/0.45            = (k4_xboole_0 @ (k1_relat_1 @ X9) @ X10))
% 0.20/0.45          | ~ (v1_relat_1 @ X9))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.45  thf(t187_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.45           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X7 : $i, X8 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ X7 @ (k1_relat_1 @ X8))
% 0.20/0.45          | ((k7_relat_1 @ X8 @ X7) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ~ (v1_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)))
% 0.20/0.45          | ((k7_relat_1 @ (k4_xboole_0 @ X1 @ (k7_relat_1 @ X1 @ X0)) @ X2)
% 0.20/0.45              = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.45            = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)))
% 0.20/0.45          | ~ (v1_relat_1 @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.45  thf(fc2_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X5 : $i, X6 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ X0)
% 0.20/0.45          | ((k7_relat_1 @ (k4_xboole_0 @ X0 @ (k7_relat_1 @ X0 @ sk_B)) @ sk_A)
% 0.20/0.45              = (k1_xboole_0)))),
% 0.20/0.45      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (((k7_relat_1 @ (k6_subset_1 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.20/0.45         != (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]: ((k6_subset_1 @ X3 @ X4) = (k4_xboole_0 @ X3 @ X4))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (((k7_relat_1 @ (k4_xboole_0 @ sk_C @ (k7_relat_1 @ sk_C @ sk_B)) @ sk_A)
% 0.20/0.45         != (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.45  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('17', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.45  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
