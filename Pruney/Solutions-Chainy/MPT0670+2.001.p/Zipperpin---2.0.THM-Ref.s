%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CoBbwQRy8o

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  63 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  377 ( 705 expanded)
%              Number of equality atoms :   10 (  27 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf(t87_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
         => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_1])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( X12
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ ( k1_funct_1 @ X11 @ X10 ) ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ ( k8_relat_1 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k8_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_B @ sk_C ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CoBbwQRy8o
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 39 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(dt_k8_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (k8_relat_1 @ X6 @ X7)) | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 0.20/0.49  thf(fc9_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 0.20/0.49         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (k8_relat_1 @ X8 @ X9))
% 0.20/0.49          | ~ (v1_funct_1 @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.49  thf(t87_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.49         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49          ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.49            ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t87_funct_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t8_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.49           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.49          | ((X12) != (k1_funct_1 @ X11 @ X10))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X11)
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X10 @ (k1_funct_1 @ X11 @ X10)) @ X11)
% 0.20/0.49          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((r2_hidden @ 
% 0.20/0.49         (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49         (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | ~ (v1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           (k8_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '6'])).
% 0.20/0.49  thf('8', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           (k8_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           (k8_relat_1 @ sk_B @ sk_C)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '10'])).
% 0.20/0.49  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49        (k8_relat_1 @ sk_B @ sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(d12_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ C ) =>
% 0.20/0.49           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.20/0.49             ( ![D:$i,E:$i]:
% 0.20/0.49               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.20/0.49                 ( ( r2_hidden @ E @ A ) & 
% 0.20/0.49                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((X0) != (k8_relat_1 @ X1 @ X2))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i, X3 : $i, X5 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k8_relat_1 @ X1 @ X2))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X2)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           sk_C)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('17', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k8_relat_1 @ sk_B @ sk_C))
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           sk_C))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | (r2_hidden @ 
% 0.20/0.49           (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49           sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((r2_hidden @ 
% 0.20/0.49        (k4_tarski @ sk_A @ (k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)) @ 
% 0.20/0.49        sk_C)),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.20/0.49          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.20/0.49          | ~ (v1_funct_1 @ X11)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49        | ((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.20/0.49            = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.20/0.49         = (k1_funct_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((k1_funct_1 @ (k8_relat_1 @ sk_B @ sk_C) @ sk_A)
% 0.20/0.49         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
