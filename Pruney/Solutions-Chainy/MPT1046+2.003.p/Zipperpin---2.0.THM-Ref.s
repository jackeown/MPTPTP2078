%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ciz0DrNgy6

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  60 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  255 ( 695 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(t162_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
        = ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
          = ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_partfun1 @ X2 @ X3 )
      | ( ( k5_partfun1 @ X3 @ X4 @ X2 )
        = ( k1_tarski @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('2',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ~ ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ~ ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k3_partfun1 @ X5 @ X6 @ X7 )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    ~ ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k3_partfun1 @ B @ A @ A ) )
        & ( v1_partfun1 @ ( k3_partfun1 @ B @ A @ A ) @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_partfun1 @ ( k3_partfun1 @ X0 @ X1 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k3_partfun1 @ sk_B @ sk_A @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['8','9'])).

thf('19',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['12','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ciz0DrNgy6
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:52:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 13 iterations in 0.011s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(k3_partfun1_type, type, k3_partfun1: $i > $i > $i > $i).
% 0.20/0.46  thf(t162_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46       ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.20/0.46         ( k1_tarski @ B ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46          ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) ) =
% 0.20/0.46            ( k1_tarski @ B ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t162_funct_2])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t174_partfun1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ( v1_partfun1 @ C @ A ) <=>
% 0.20/0.46         ( ( k5_partfun1 @ A @ B @ C ) = ( k1_tarski @ C ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (v1_partfun1 @ X2 @ X3)
% 0.20/0.46          | ((k5_partfun1 @ X3 @ X4 @ X2) = (k1_tarski @ X2))
% 0.20/0.46          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.20/0.46          | ~ (v1_funct_1 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [t174_partfun1])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ((k5_partfun1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.46        | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.46  thf('3', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      ((((k5_partfun1 @ sk_A @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.46        | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (((k5_partfun1 @ sk_A @ sk_A @ (k3_partfun1 @ sk_B @ sk_A @ sk_A))
% 0.20/0.46         != (k1_tarski @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t87_partfun1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ( k3_partfun1 @ C @ A @ B ) = ( C ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.46         (((k3_partfun1 @ X5 @ X6 @ X7) = (X5))
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.20/0.46          | ~ (v1_funct_1 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t87_partfun1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      ((~ (v1_funct_1 @ sk_B) | ((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('10', plain, (((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((k5_partfun1 @ sk_A @ sk_A @ sk_B) != (k1_tarski @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '10'])).
% 0.20/0.46  thf('12', plain, (~ (v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['4', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(fc9_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46       ( ( v1_funct_1 @ ( k3_partfun1 @ B @ A @ A ) ) & 
% 0.20/0.46         ( v1_partfun1 @ ( k3_partfun1 @ B @ A @ A ) @ A ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((v1_partfun1 @ (k3_partfun1 @ X0 @ X1 @ X1) @ X1)
% 0.20/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X1)))
% 0.20/0.46          | ~ (v1_funct_2 @ X0 @ X1 @ X1)
% 0.20/0.46          | ~ (v1_funct_1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc9_funct_2])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.46        | (v1_partfun1 @ (k3_partfun1 @ sk_B @ sk_A @ sk_A) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('18', plain, (((k3_partfun1 @ sk_B @ sk_A @ sk_A) = (sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('19', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.20/0.46  thf('20', plain, ($false), inference('demod', [status(thm)], ['12', '19'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
