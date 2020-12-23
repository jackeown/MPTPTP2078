%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GCG0vpzFVj

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  406 (1186 expanded)
%              Number of equality atoms :   10 (  36 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t115_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_F @ X2 @ X3 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k7_relset_1 @ X5 @ X6 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D @ X7 ) )
      | ~ ( r2_hidden @ X7 @ sk_C )
      | ~ ( m1_subset_1 @ X7 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_F @ X2 @ X3 @ X4 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X2 @ ( k7_relset_1 @ X5 @ X6 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['10','16'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('19',plain,(
    m1_subset_1 @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X2
        = ( k1_funct_1 @ X3 @ ( sk_F @ X2 @ X3 @ X4 @ X5 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k7_relset_1 @ X5 @ X6 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X5 @ X6 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t115_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ( X1
        = ( k1_funct_1 @ sk_D @ ( sk_F @ X1 @ sk_D @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D @ ( sk_F @ sk_E @ sk_D @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['9','19','27'])).

thf('29',plain,(
    $false ),
    inference(simplify,[status(thm)],['28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GCG0vpzFVj
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 16 iterations in 0.014s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.46  thf(t116_funct_2, conjecture,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46       ( ![E:$i]:
% 0.19/0.46         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.19/0.46              ( ![F:$i]:
% 0.19/0.46                ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.46                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.19/0.46                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46          ( ![E:$i]:
% 0.19/0.46            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.19/0.46                 ( ![F:$i]:
% 0.19/0.46                   ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.46                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.19/0.46                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t115_funct_2, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.46       ( ![E:$i]:
% 0.19/0.46         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.19/0.46              ( ![F:$i]:
% 0.19/0.46                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.19/0.46                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         ((r2_hidden @ (sk_F @ X2 @ X3 @ X4 @ X5) @ X4)
% 0.19/0.46          | ~ (r2_hidden @ X2 @ (k7_relset_1 @ X5 @ X6 @ X3 @ X4))
% 0.19/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.19/0.46          | ~ (v1_funct_2 @ X3 @ X5 @ X6)
% 0.19/0.46          | ~ (v1_funct_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_funct_1 @ sk_D)
% 0.19/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.19/0.46          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ X0))),
% 0.19/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.46  thf('7', plain, ((r2_hidden @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A) @ sk_C)),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X7 : $i]:
% 0.19/0.46         (((sk_E) != (k1_funct_1 @ sk_D @ X7))
% 0.19/0.46          | ~ (r2_hidden @ X7 @ sk_C)
% 0.19/0.46          | ~ (m1_subset_1 @ X7 @ sk_A))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      ((~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)
% 0.19/0.46        | ((sk_E) != (k1_funct_1 @ sk_D @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         ((r2_hidden @ (sk_F @ X2 @ X3 @ X4 @ X5) @ X5)
% 0.19/0.46          | ~ (r2_hidden @ X2 @ (k7_relset_1 @ X5 @ X6 @ X3 @ X4))
% 0.19/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.19/0.46          | ~ (v1_funct_2 @ X3 @ X5 @ X6)
% 0.19/0.46          | ~ (v1_funct_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_funct_1 @ sk_D)
% 0.19/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.19/0.46          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | (r2_hidden @ (sk_F @ X1 @ sk_D @ X0 @ sk_A) @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.19/0.46  thf('17', plain, ((r2_hidden @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['10', '16'])).
% 0.19/0.46  thf(t1_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.46  thf('19', plain, ((m1_subset_1 @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A) @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         (((X2) = (k1_funct_1 @ X3 @ (sk_F @ X2 @ X3 @ X4 @ X5)))
% 0.19/0.46          | ~ (r2_hidden @ X2 @ (k7_relset_1 @ X5 @ X6 @ X3 @ X4))
% 0.19/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6)))
% 0.19/0.46          | ~ (v1_funct_2 @ X3 @ X5 @ X6)
% 0.19/0.46          | ~ (v1_funct_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t115_funct_2])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_funct_1 @ sk_D)
% 0.19/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.19/0.46          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | ((X1) = (k1_funct_1 @ sk_D @ (sk_F @ X1 @ sk_D @ X0 @ sk_A))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0))
% 0.19/0.46          | ((X1) = (k1_funct_1 @ sk_D @ (sk_F @ X1 @ sk_D @ X0 @ sk_A))))),
% 0.19/0.46      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.46  thf('27', plain,
% 0.19/0.46      (((sk_E) = (k1_funct_1 @ sk_D @ (sk_F @ sk_E @ sk_D @ sk_C @ sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['20', '26'])).
% 0.19/0.46  thf('28', plain, (((sk_E) != (sk_E))),
% 0.19/0.46      inference('demod', [status(thm)], ['9', '19', '27'])).
% 0.19/0.46  thf('29', plain, ($false), inference('simplify', [status(thm)], ['28'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
