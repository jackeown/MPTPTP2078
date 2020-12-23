%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ouJeT7lsIV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:57 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  308 ( 938 expanded)
%              Number of equality atoms :    7 (  29 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C )
   <= ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['4','7','8'])).

thf('10',plain,(
    ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['15','18'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v1_funct_2 @ X11 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['21','22','23','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['10','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ouJeT7lsIV
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:17:49 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.24/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.49  % Solved by: fo/fo7.sh
% 0.24/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.49  % done 25 iterations in 0.012s
% 0.24/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.49  % SZS output start Refutation
% 0.24/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.24/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.49  thf(t130_funct_2, conjecture,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.49       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.24/0.49         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.49           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.24/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.49        ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.49            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.49          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.24/0.49            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.49              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.24/0.49    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.24/0.49  thf('0', plain,
% 0.24/0.49      ((~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.24/0.49        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('1', plain,
% 0.24/0.49      ((~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))
% 0.24/0.49         <= (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('3', plain, ((~ (v1_funct_1 @ sk_C)) <= (~ ((v1_funct_1 @ sk_C)))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('4', plain, (((v1_funct_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.49  thf('5', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('6', plain,
% 0.24/0.49      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.24/0.49         <= (~
% 0.24/0.49             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('7', plain,
% 0.24/0.49      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.24/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.24/0.49  thf('8', plain,
% 0.24/0.49      (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.24/0.49       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.24/0.49       ~ ((v1_funct_1 @ sk_C))),
% 0.24/0.49      inference('split', [status(esa)], ['0'])).
% 0.24/0.49  thf('9', plain, (~ ((v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.24/0.49      inference('sat_resolution*', [status(thm)], ['4', '7', '8'])).
% 0.24/0.49  thf('10', plain, (~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.24/0.49      inference('simpl_trail', [status(thm)], ['1', '9'])).
% 0.24/0.49  thf('11', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(cc2_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.49  thf('12', plain,
% 0.24/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.24/0.49         ((v5_relat_1 @ X5 @ X7)
% 0.24/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.24/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.49  thf('13', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.24/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.49  thf(d19_relat_1, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( v1_relat_1 @ B ) =>
% 0.24/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.49  thf('14', plain,
% 0.24/0.49      (![X0 : $i, X1 : $i]:
% 0.24/0.49         (~ (v5_relat_1 @ X0 @ X1)
% 0.24/0.49          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.24/0.49          | ~ (v1_relat_1 @ X0))),
% 0.24/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.24/0.49  thf('15', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.24/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.49  thf('16', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(cc1_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( v1_relat_1 @ C ) ))).
% 0.24/0.49  thf('17', plain,
% 0.24/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.24/0.49         ((v1_relat_1 @ X2)
% 0.24/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.24/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.49  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.49  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.24/0.49      inference('demod', [status(thm)], ['15', '18'])).
% 0.24/0.49  thf(t4_funct_2, axiom,
% 0.24/0.49    (![A:$i,B:$i]:
% 0.24/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.24/0.49         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.24/0.49           ( m1_subset_1 @
% 0.24/0.49             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.24/0.49  thf('20', plain,
% 0.24/0.49      (![X11 : $i, X12 : $i]:
% 0.24/0.49         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.24/0.49          | (v1_funct_2 @ X11 @ (k1_relat_1 @ X11) @ X12)
% 0.24/0.49          | ~ (v1_funct_1 @ X11)
% 0.24/0.49          | ~ (v1_relat_1 @ X11))),
% 0.24/0.49      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.24/0.49  thf('21', plain,
% 0.24/0.49      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.49        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.49        | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.24/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.49  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.49  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('24', plain,
% 0.24/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.24/0.49    (![A:$i,B:$i,C:$i]:
% 0.24/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.24/0.49  thf('25', plain,
% 0.24/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.49         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.24/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.24/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.24/0.49  thf('26', plain,
% 0.24/0.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.24/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.49  thf('27', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_A))),
% 0.24/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.49  thf('28', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 0.24/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.24/0.49  thf('29', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.24/0.49      inference('demod', [status(thm)], ['21', '22', '23', '28'])).
% 0.24/0.49  thf('30', plain, ($false), inference('demod', [status(thm)], ['10', '29'])).
% 0.24/0.49  
% 0.24/0.49  % SZS output end Refutation
% 0.24/0.49  
% 0.24/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
