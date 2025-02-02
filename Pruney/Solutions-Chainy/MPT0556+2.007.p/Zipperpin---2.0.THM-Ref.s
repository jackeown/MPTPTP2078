%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RVI4P5y51T

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   41 (  65 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  276 ( 610 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t157_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X11 @ X12 ) @ ( k9_relat_1 @ X10 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t157_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k9_relat_1 @ X9 @ X7 ) @ ( k9_relat_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k2_xboole_0 @ X1 @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_D @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k9_relat_1 @ sk_D @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X2 @ ( k2_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_C @ X1 ) @ ( k2_xboole_0 @ ( k9_relat_1 @ sk_D @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RVI4P5y51T
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 113 iterations in 0.055s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(t158_relat_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ D ) =>
% 0.21/0.50           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.50             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.50        ( ( v1_relat_1 @ C ) =>
% 0.21/0.50          ( ![D:$i]:
% 0.21/0.50            ( ( v1_relat_1 @ D ) =>
% 0.21/0.50              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.21/0.50                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t157_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ C ) =>
% 0.21/0.50           ( ( r1_tarski @ B @ C ) =>
% 0.21/0.50             ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X10)
% 0.21/0.50          | (r1_tarski @ (k9_relat_1 @ X11 @ X12) @ (k9_relat_1 @ X10 @ X12))
% 0.21/0.50          | ~ (r1_tarski @ X11 @ X10)
% 0.21/0.50          | ~ (v1_relat_1 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [t157_relat_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ sk_C)
% 0.21/0.50          | (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k2_xboole_0 @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))
% 0.21/0.50           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t156_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ C ) =>
% 0.21/0.50       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.50         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X9)
% 0.21/0.50          | (r1_tarski @ (k9_relat_1 @ X9 @ X7) @ (k9_relat_1 @ X9 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.50  thf(t10_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.21/0.50             (k2_xboole_0 @ X1 @ (k9_relat_1 @ X0 @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (((r1_tarski @ (k9_relat_1 @ sk_D @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_D))),
% 0.21/0.50      inference('sup+', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((r1_tarski @ (k9_relat_1 @ sk_D @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((k2_xboole_0 @ (k9_relat_1 @ sk_D @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))
% 0.21/0.50         = (k9_relat_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ X2 @ (k2_xboole_0 @ X4 @ X3)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (r1_tarski @ (k9_relat_1 @ sk_C @ X0) @ 
% 0.21/0.50          (k2_xboole_0 @ X1 @ (k9_relat_1 @ sk_D @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (r1_tarski @ (k9_relat_1 @ sk_C @ X1) @ 
% 0.21/0.50          (k2_xboole_0 @ (k9_relat_1 @ sk_D @ X1) @ X0))),
% 0.21/0.50      inference('sup+', [status(thm)], ['19', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 0.21/0.50      inference('sup+', [status(thm)], ['18', '23'])).
% 0.21/0.50  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
