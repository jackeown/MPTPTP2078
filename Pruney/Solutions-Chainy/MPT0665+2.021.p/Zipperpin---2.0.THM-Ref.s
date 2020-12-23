%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A8eJti9VVb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  322 ( 714 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t73_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ A @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
            & ( r2_hidden @ A @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X9 @ X8 ) @ X7 )
        = ( k1_funct_1 @ X9 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t72_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X5 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['0','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A8eJti9VVb
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:22:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 35 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(t73_funct_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.21/0.49         ( r2_hidden @
% 0.21/0.49           ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.49        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49          ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & ( r2_hidden @ A @ B ) ) =>
% 0.21/0.49            ( r2_hidden @
% 0.21/0.49              ( k1_funct_1 @ C @ A ) @ ( k2_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t73_funct_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.21/0.49          (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t72_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.49          | ~ (v1_relat_1 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X9)
% 0.21/0.49          | ((k1_funct_1 @ (k7_relat_1 @ X9 @ X8) @ X7)
% 0.21/0.49              = (k1_funct_1 @ X9 @ X7)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t72_funct_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.21/0.49            = (k1_funct_1 @ X0 @ sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(fc8_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.49       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.49         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3)
% 0.21/0.49          | (v1_funct_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3)
% 0.21/0.49          | (v1_relat_1 @ (k7_relat_1 @ X3 @ X4)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.21/0.49  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t86_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ C ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.21/0.49         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.21/0.49          | (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 0.21/0.49          | ~ (v1_relat_1 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ sk_C)
% 0.21/0.49          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.21/0.49          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.21/0.49          | ~ (r2_hidden @ sk_A @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '11'])).
% 0.21/0.49  thf(t12_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.49         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X6))
% 0.21/0.49          | (r2_hidden @ (k1_funct_1 @ X6 @ X5) @ (k2_relat_1 @ X6))
% 0.21/0.49          | ~ (v1_funct_1 @ X6)
% 0.21/0.49          | ~ (v1_relat_1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B))
% 0.21/0.49        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '14'])).
% 0.21/0.49  thf('16', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.21/0.49         (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.21/0.49        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.49        | (r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.21/0.49           (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '18'])).
% 0.21/0.49  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      ((r2_hidden @ (k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) @ 
% 0.21/0.49        (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.21/0.49         (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.49      inference('sup+', [status(thm)], ['3', '22'])).
% 0.21/0.49  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.21/0.49        (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.49  thf('27', plain, ($false), inference('demod', [status(thm)], ['0', '26'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
