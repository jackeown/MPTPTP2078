%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QqLxtBsj9n

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:59 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   60 (  76 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 751 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','14','17'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v5_relat_1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QqLxtBsj9n
% 0.12/0.32  % Computer   : n019.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:22:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 46 iterations in 0.047s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.49  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.18/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.18/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.18/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.49  thf(t7_funct_2, conjecture,
% 0.18/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.18/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.49       ( ( r2_hidden @ C @ A ) =>
% 0.18/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.18/0.49           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.18/0.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.18/0.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.18/0.49          ( ( r2_hidden @ C @ A ) =>
% 0.18/0.49            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.18/0.49              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.18/0.49  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc2_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.49         ((v5_relat_1 @ X6 @ X8)
% 0.18/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.49  thf('4', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.49  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(d1_funct_2, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.18/0.49           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.18/0.49             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.18/0.49         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.18/0.49           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.18/0.49             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_1, axiom,
% 0.18/0.49    (![C:$i,B:$i,A:$i]:
% 0.18/0.49     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.18/0.49       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.18/0.49         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.18/0.49          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.18/0.49          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.18/0.49  thf('7', plain,
% 0.18/0.49      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.18/0.49        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.49  thf(zf_stmt_2, axiom,
% 0.18/0.49    (![B:$i,A:$i]:
% 0.18/0.49     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.18/0.49       ( zip_tseitin_0 @ B @ A ) ))).
% 0.18/0.49  thf('8', plain,
% 0.18/0.49      (![X12 : $i, X13 : $i]:
% 0.18/0.49         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.18/0.49  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.18/0.49  thf(zf_stmt_5, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.18/0.49         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.18/0.49           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.18/0.49             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.18/0.49         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.18/0.49          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.18/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.18/0.49  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('14', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.18/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.18/0.49         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.18/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.18/0.49  thf('17', plain,
% 0.18/0.49      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.18/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.49  thf('18', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.18/0.49      inference('demod', [status(thm)], ['7', '14', '17'])).
% 0.18/0.49  thf(t172_funct_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.18/0.49       ( ![C:$i]:
% 0.18/0.49         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.18/0.49           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.18/0.49          | (r2_hidden @ (k1_funct_1 @ X1 @ X0) @ X2)
% 0.18/0.49          | ~ (v1_funct_1 @ X1)
% 0.18/0.49          | ~ (v5_relat_1 @ X1 @ X2)
% 0.18/0.49          | ~ (v1_relat_1 @ X1))),
% 0.18/0.49      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.18/0.49  thf('20', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.18/0.49          | ~ (v1_relat_1 @ sk_D)
% 0.18/0.49          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.18/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.18/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.18/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.49  thf('21', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc1_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( v1_relat_1 @ C ) ))).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.49         ((v1_relat_1 @ X3)
% 0.18/0.49          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.18/0.49  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.18/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.18/0.49  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('25', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.18/0.49          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.18/0.49          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.18/0.49      inference('demod', [status(thm)], ['20', '23', '24'])).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ sk_B)
% 0.18/0.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.18/0.49      inference('sup-', [status(thm)], ['4', '25'])).
% 0.18/0.49  thf('27', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['1', '26'])).
% 0.18/0.49  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
