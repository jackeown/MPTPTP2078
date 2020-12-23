%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPWWvvNd3R

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:03 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  214 ( 256 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k7_relat_1 @ X10 @ X9 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X9 ) @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( ( k5_relat_1 @ X7 @ ( k6_relat_1 @ X8 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X3 @ X4 ) )
        = ( k9_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('14',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,
    ( sk_B
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dPWWvvNd3R
% 0.17/0.39  % Computer   : n007.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 18:55:21 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.25/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.51  % Solved by: fo/fo7.sh
% 0.25/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.51  % done 16 iterations in 0.011s
% 0.25/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.51  % SZS output start Refutation
% 0.25/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.25/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.25/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.25/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.25/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.25/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.51  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.25/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.25/0.51  thf(t94_relat_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ B ) =>
% 0.25/0.51       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.25/0.51  thf('0', plain,
% 0.25/0.51      (![X9 : $i, X10 : $i]:
% 0.25/0.51         (((k7_relat_1 @ X10 @ X9) = (k5_relat_1 @ (k6_relat_1 @ X9) @ X10))
% 0.25/0.51          | ~ (v1_relat_1 @ X10))),
% 0.25/0.51      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.25/0.51  thf(t162_funct_1, conjecture,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.51       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.25/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.51    (~( ![A:$i,B:$i]:
% 0.25/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.51          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.25/0.51    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.25/0.51  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf(t3_subset, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.25/0.51  thf('2', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.25/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.25/0.51  thf('3', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.25/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.25/0.51  thf(t71_relat_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.25/0.51       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.25/0.51  thf('4', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.25/0.51  thf(t79_relat_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ B ) =>
% 0.25/0.51       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.25/0.51         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.25/0.51  thf('5', plain,
% 0.25/0.51      (![X7 : $i, X8 : $i]:
% 0.25/0.51         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.25/0.51          | ((k5_relat_1 @ X7 @ (k6_relat_1 @ X8)) = (X7))
% 0.25/0.51          | ~ (v1_relat_1 @ X7))),
% 0.25/0.51      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.25/0.51  thf('6', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.25/0.51          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.25/0.51          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.25/0.51              = (k6_relat_1 @ X0)))),
% 0.25/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.51  thf(fc3_funct_1, axiom,
% 0.25/0.51    (![A:$i]:
% 0.25/0.51     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.25/0.51       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.25/0.51  thf('7', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.25/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.25/0.51  thf('8', plain,
% 0.25/0.51      (![X0 : $i, X1 : $i]:
% 0.25/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.25/0.51          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.25/0.51              = (k6_relat_1 @ X0)))),
% 0.25/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.25/0.51  thf('9', plain,
% 0.25/0.51      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.25/0.51         = (k6_relat_1 @ sk_B))),
% 0.25/0.51      inference('sup-', [status(thm)], ['3', '8'])).
% 0.25/0.51  thf('10', plain,
% 0.25/0.51      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))
% 0.25/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.25/0.51      inference('sup+', [status(thm)], ['0', '9'])).
% 0.25/0.51  thf('11', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.25/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.25/0.51  thf('12', plain,
% 0.25/0.51      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.25/0.51  thf(t148_relat_1, axiom,
% 0.25/0.51    (![A:$i,B:$i]:
% 0.25/0.51     ( ( v1_relat_1 @ B ) =>
% 0.25/0.51       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.25/0.51  thf('13', plain,
% 0.25/0.51      (![X3 : $i, X4 : $i]:
% 0.25/0.51         (((k2_relat_1 @ (k7_relat_1 @ X3 @ X4)) = (k9_relat_1 @ X3 @ X4))
% 0.25/0.51          | ~ (v1_relat_1 @ X3))),
% 0.25/0.51      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.25/0.51  thf('14', plain,
% 0.25/0.51      ((((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 0.25/0.51          = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))
% 0.25/0.51        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.25/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.25/0.51  thf('15', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 0.25/0.51      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.25/0.51  thf('16', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.25/0.51      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.25/0.51  thf('17', plain, (((sk_B) = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 0.25/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.25/0.51  thf('18', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.25/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.51  thf('19', plain, ($false),
% 0.25/0.51      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.25/0.51  
% 0.25/0.51  % SZS output end Refutation
% 0.25/0.51  
% 0.25/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
